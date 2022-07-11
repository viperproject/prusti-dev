use super::{
    super::ast::{
        expression::{
            visitors::{
                default_fold_expression, default_fold_quantifier, default_walk_expression,
                ExpressionFolder, ExpressionWalker,
            },
            *,
        },
        position::Position,
        ty::{self, visitors::TypeFolder, LifetimeConst, Type},
    },
    ty::Typed,
};

impl From<VariableDecl> for Expression {
    fn from(variable: VariableDecl) -> Self {
        Self::local_no_pos(variable)
    }
}

impl BinaryOpKind {
    pub fn get_result_type(self, argument_type: &Type) -> &Type {
        match self {
            BinaryOpKind::EqCmp
            | BinaryOpKind::NeCmp
            | BinaryOpKind::GtCmp
            | BinaryOpKind::GeCmp
            | BinaryOpKind::LtCmp
            | BinaryOpKind::LeCmp
            | BinaryOpKind::And
            | BinaryOpKind::Or
            | BinaryOpKind::Implies => &Type::Bool,
            BinaryOpKind::Add
            | BinaryOpKind::Sub
            | BinaryOpKind::Mul
            | BinaryOpKind::Div
            | BinaryOpKind::Mod
            | BinaryOpKind::LifetimeIntersection => argument_type,
        }
    }
}

impl Expression {
    /// Only defined for places.
    pub fn get_base(&self) -> VariableDecl {
        debug_assert!(self.is_place());
        match self {
            Expression::Local(Local { variable, .. }) => variable.clone(),
            Expression::LabelledOld(LabelledOld { base, .. }) => base.get_base(),
            _ => self.get_parent_ref().unwrap().get_base(),
        }
    }
    /// Only defined for places.
    pub fn get_parent_ref(&self) -> Option<&Expression> {
        debug_assert!(self.is_place());
        match self {
            Expression::Local(_) => None,
            Expression::Variant(Variant { box ref base, .. })
            | Expression::Field(Field { box ref base, .. })
            | Expression::Deref(Deref { box ref base, .. })
            | Expression::AddrOf(AddrOf { box ref base, .. }) => Some(base),
            Expression::LabelledOld(_) => None,
            Expression::BuiltinFuncApp(BuiltinFuncApp {
                function: BuiltinFunc::Index,
                arguments,
                ..
            }) => Some(&arguments[0]),
            expr => unreachable!("{}", expr),
        }
    }
    pub fn iter_prefixes(&self) -> impl Iterator<Item = &Expression> {
        struct PrefixIterator<'a> {
            expr: Option<&'a Expression>,
        }
        impl<'a> Iterator for PrefixIterator<'a> {
            type Item = &'a Expression;
            fn next(&mut self) -> Option<Self::Item> {
                if let Some(current) = self.expr.take() {
                    self.expr = current.get_parent_ref();
                    Some(current)
                } else {
                    None
                }
            }
        }
        PrefixIterator { expr: Some(self) }
    }
    pub fn is_place(&self) -> bool {
        match self {
            Expression::Local(_) => true,
            Expression::Variant(Variant { base, .. })
            | Expression::Field(Field { base, .. })
            | Expression::Deref(Deref { base, .. })
            | Expression::AddrOf(AddrOf { base, .. })
            | Expression::LabelledOld(LabelledOld { base, .. }) => base.is_place(),
            Expression::BuiltinFuncApp(BuiltinFuncApp {
                function: BuiltinFunc::Index,
                arguments,
                ..
            }) if arguments.len() == 2 => arguments[0].is_place() && arguments[1].is_place(),
            _ => false,
        }
    }
    /// Check whether the place is a dereference of a reference and if that is
    /// the case, returns the uniqueness guarantees given by this reference.
    pub fn get_dereference_kind(&self) -> Option<(ty::LifetimeConst, ty::Uniqueness)> {
        assert!(self.is_place());
        if let Some(parent) = self.get_parent_ref() {
            if let Some(result) = parent.get_dereference_kind() {
                return Some(result);
            } else if self.is_deref() {
                if let Type::Reference(ty::Reference {
                    lifetime,
                    uniqueness,
                    ..
                }) = parent.get_type()
                {
                    return Some((lifetime.clone(), *uniqueness));
                } else {
                    unreachable!();
                }
            }
        }
        None
    }

    pub fn is_deref_of_lifetime(&self, searched_lifetime: &ty::LifetimeConst) -> bool {
        if let Some(parent) = self.get_parent_ref() {
            if self.is_deref() {
                if let Type::Reference(ty::Reference { lifetime, .. }) = parent.get_type() {
                    return searched_lifetime == lifetime
                        || parent.is_deref_of_lifetime(searched_lifetime);
                }
            }
            parent.is_deref_of_lifetime(searched_lifetime)
        } else {
            false
        }
    }

    /// Check whether the place is a dereference of a reference and if that is
    /// the case, return its base.
    pub fn get_dereference_base(&self) -> Option<&Expression> {
        assert!(self.is_place());
        if let Expression::Deref(Deref { box base, .. }) = self {
            Some(base)
        } else if let Some(parent) = self.get_parent_ref() {
            parent.get_dereference_base()
        } else {
            None
        }
    }

    #[must_use]
    pub fn erase_lifetime(self) -> Expression {
        struct DefaultLifetimeEraser {}
        impl ExpressionFolder for DefaultLifetimeEraser {
            fn fold_type(&mut self, ty: Type) -> Type {
                ty.erase_lifetimes()
            }
            fn fold_variable_decl(&mut self, variable_decl: VariableDecl) -> VariableDecl {
                VariableDecl {
                    name: variable_decl.name,
                    ty: variable_decl.ty.erase_lifetimes(),
                }
            }
            fn fold_field_decl(&mut self, field_decl: FieldDecl) -> FieldDecl {
                // FIXME: Fix the visitor generator to follow relative imports
                // when generating visitors.
                FieldDecl {
                    ty: field_decl.ty.erase_lifetimes(),
                    ..field_decl
                }
            }
        }
        DefaultLifetimeEraser {}.fold_expression(self)
    }

    #[must_use]
    pub fn replace_place(self, target: &Expression, replacement: &Expression) -> Self {
        debug_assert!(target.is_place());
        if let Some(ty) = replacement.get_type().forget_variant() {
            assert_eq!(target.get_type(), &ty, "{} → {}", target, replacement);
        } else {
            assert_eq!(
                target.get_type(),
                replacement.get_type(),
                "{} → {}",
                target,
                replacement
            );
        }

        struct PlaceReplacer<'a> {
            target: &'a Expression,
            replacement: &'a Expression,
        }
        impl<'a> ExpressionFolder for PlaceReplacer<'a> {
            fn fold_expression(&mut self, expression: Expression) -> Expression {
                if expression.is_place() && &expression == self.target {
                    self.replacement.clone()
                } else {
                    default_fold_expression(self, expression)
                }
            }
        }
        let mut replacer = PlaceReplacer {
            target,
            replacement,
        };
        replacer.fold_expression(self)
    }
    #[must_use]
    pub fn replace_multiple_places(self, replacements: &[(Expression, Expression)]) -> Self {
        struct PlaceReplacer<'a> {
            replacements: &'a [(Expression, Expression)],
        }
        impl<'a> ExpressionFolder for PlaceReplacer<'a> {
            fn fold_expression(&mut self, expression: Expression) -> Expression {
                if expression.is_place() {
                    // Check if this matches a substitution.
                    for (target, replacement) in self.replacements {
                        if target == &expression {
                            return replacement.clone();
                        }
                    }
                }
                // Otherwise, keep folding
                default_fold_expression(self, expression)
            }

            fn fold_quantifier_enum(&mut self, quantifier: Quantifier) -> Expression {
                // TODO: the correct solution is the following:
                // (1) skip replacements where `src` uses a quantified variable;
                // (2) rename with a fresh name the quantified variables that conflict with `dst`.
                for (src, dst) in self.replacements.iter() {
                    if quantifier.variables.contains(&src.get_base())
                        || quantifier.variables.contains(&dst.get_base())
                    {
                        unimplemented!(
                            "replace_multiple_places doesn't handle replacements that conflict \
                            with quantified variables"
                        )
                    }
                }
                Expression::Quantifier(default_fold_quantifier(self, quantifier))
            }
        }
        PlaceReplacer { replacements }.fold_expression(self)
    }
    #[must_use]
    pub fn map_old_expression_label<F>(self, substitutor: F) -> Self
    where
        F: Fn(String) -> String,
    {
        struct OldExpressionLabelSubstitutor<T>
        where
            T: Fn(String) -> String,
        {
            substitutor: T,
        }
        impl<T> ExpressionFolder for OldExpressionLabelSubstitutor<T>
        where
            T: Fn(String) -> String,
        {
            fn fold_labelled_old(
                &mut self,
                LabelledOld {
                    label,
                    base,
                    position,
                }: LabelledOld,
            ) -> LabelledOld {
                LabelledOld {
                    label: (self.substitutor)(label),
                    base,
                    position,
                }
            }
        }
        OldExpressionLabelSubstitutor { substitutor }.fold_expression(self)
    }
    /// Simplify `Deref(AddrOf(P))` to `P`.
    #[must_use]
    pub fn simplify_addr_of(self) -> Self {
        struct Simplifier;
        impl ExpressionFolder for Simplifier {
            fn fold_field_enum(
                &mut self,
                Field {
                    base: receiver,
                    field,
                    position,
                }: Field,
            ) -> Expression {
                if let Expression::AddrOf(AddrOf { base, .. }) = *receiver {
                    *base
                } else {
                    Expression::field(self.fold_expression(*receiver), field, position)
                }
            }
        }
        Simplifier.fold_expression(self)
    }
    fn apply_simplification_rules(self) -> Self {
        let mut expression = self;
        loop {
            expression = match expression {
                Expression::Deref(Deref {
                    base: box Expression::AddrOf(AddrOf { base, .. }),
                    ..
                }) => *base,
                Expression::Field(Field {
                    field,
                    base: box Expression::Constructor(Constructor { arguments, .. }),
                    ..
                }) => arguments[field.index].clone(),
                Expression::BinaryOp(BinaryOp {
                    op_kind,
                    left:
                        box Expression::AddrOf(AddrOf {
                            base: left,
                            ty:
                                Type::Reference(ty::Reference {
                                    lifetime: _,
                                    uniqueness: ty::Uniqueness::Shared,
                                    target_type:
                                        box Type::Map(_) | box Type::Sequence(_) | box Type::Int(_),
                                }),
                            ..
                        }),
                    right:
                        box Expression::AddrOf(AddrOf {
                            base: right,
                            ty:
                                Type::Reference(ty::Reference {
                                    lifetime: _,
                                    uniqueness: ty::Uniqueness::Shared,
                                    target_type:
                                        box Type::Map(_) | box Type::Sequence(_) | box Type::Int(_),
                                }),
                            ..
                        }),
                    position,
                }) => Expression::BinaryOp(BinaryOp {
                    op_kind,
                    left,
                    right,
                    position,
                }),
                Expression::UnaryOp(UnaryOp {
                    op_kind: op_kind_outer,
                    argument:
                        box Expression::UnaryOp(UnaryOp {
                            op_kind: op_kind_inner,
                            argument,
                            ..
                        }),
                    ..
                }) if op_kind_inner == op_kind_outer => *argument,
                Expression::Deref(Deref {
                    base: box Expression::BuiltinFuncApp(ref app),
                    ..
                }) => match app.function {
                    BuiltinFunc::LookupMap | BuiltinFunc::LookupSeq => {
                        match (&app.arguments[0], &app.return_type) {
                            (
                                Expression::AddrOf(AddrOf { base, .. }),
                                Type::Reference(ty::Reference {
                                    target_type: box return_type,
                                    ..
                                }),
                            ) => {
                                let mut arguments = app.arguments.clone();
                                arguments[0] = (**base).clone();
                                let return_type = return_type.clone();
                                Expression::BuiltinFuncApp(BuiltinFuncApp {
                                    arguments,
                                    return_type,
                                    ..app.clone()
                                })
                            }
                            _ => break expression,
                        }
                    }
                    _ => break expression,
                },
                _ => {
                    break expression;
                }
            };
        }
    }
    pub fn simplify(self) -> Self {
        struct Simplifier;
        impl ExpressionFolder for Simplifier {
            fn fold_expression(&mut self, expression: Expression) -> Expression {
                let expression = expression.apply_simplification_rules();
                let expression = default_fold_expression(self, expression);
                expression.apply_simplification_rules()
            }
        }
        Simplifier.fold_expression(self)
    }
    pub fn find(&self, sub_target: &Expression) -> bool {
        pub struct ExprFinder<'a> {
            sub_target: &'a Expression,
            found: bool,
        }
        impl<'a> ExpressionWalker for ExprFinder<'a> {
            fn walk_expression(&mut self, expr: &Expression) {
                if expr == self.sub_target {
                    self.found = true;
                } else {
                    default_walk_expression(self, expr)
                }
            }
        }

        let mut finder = ExprFinder {
            sub_target,
            found: false,
        };
        finder.walk_expression(self);
        finder.found
    }
    pub fn function_call<S: Into<String>>(
        name: S,
        type_arguments: Vec<Type>,
        arguments: Vec<Expression>,
        return_type: Type,
    ) -> Expression {
        let parameters = arguments
            .iter()
            .enumerate()
            .map(|(i, argument)| VariableDecl {
                name: format!("_{}", i),
                ty: argument.get_type().clone(),
            })
            .collect();
        Expression::func_app_no_pos(
            name.into(),
            type_arguments,
            arguments,
            parameters,
            return_type,
        )
    }
    #[must_use]
    pub fn set_default_position(self, new_position: Position) -> Self {
        struct DefaultPositionReplacer {
            new_position: Position,
        }
        impl ExpressionFolder for DefaultPositionReplacer {
            fn fold_position(&mut self, position: Position) -> Position {
                if position.is_default() {
                    self.new_position
                } else {
                    position
                }
            }
        }
        DefaultPositionReplacer { new_position }.fold_expression(self)
    }
    #[must_use]
    pub fn replace_position(self, new_position: Position) -> Self {
        struct PositionReplacer {
            new_position: Position,
        }
        impl ExpressionFolder for PositionReplacer {
            fn fold_position(&mut self, _position: Position) -> Position {
                self.new_position
            }
        }
        PositionReplacer { new_position }.fold_expression(self)
    }
    pub fn check_no_default_position(&self) {
        struct Checker;
        impl ExpressionWalker for Checker {
            fn walk_position(&mut self, position: &Position) {
                assert!(!position.is_default());
            }
        }
        Checker.walk_expression(self)
    }
    pub fn has_prefix(&self, potential_prefix: &Expression) -> bool {
        if self == potential_prefix {
            true
        } else {
            self.get_parent_ref()
                .map(|parent| parent.has_prefix(potential_prefix))
                .unwrap_or(false)
        }
    }

    /// Assuming that `self` is an enum and is a prefix of `guiding_place`
    /// return the variant that matches the guiding place.
    pub fn get_variant_name<'a>(&self, guiding_place: &'a Expression) -> &'a VariantIndex {
        let parent = guiding_place.get_parent_ref().unwrap();
        if self == parent {
            match guiding_place {
                Expression::Variant(Variant { variant_index, .. }) => variant_index,
                _ => unreachable!(
                    "self: {} ({}), guiding_place: {}",
                    self,
                    self.get_type(),
                    guiding_place
                ),
            }
        } else {
            self.get_variant_name(parent)
        }
    }

    pub fn into_variant(self, variant_name: VariantIndex) -> Self {
        use crate::common::position::Positioned;
        let ty = self.get_type().clone().variant(variant_name.clone());
        let position = self.position();
        self.variant(variant_name, ty, position)
    }

    /// Assuming that `self` is an array and is a prefix of `guiding_place`,
    /// return the index that matches the guiding place.
    pub fn get_index<'a>(&self, guiding_place: &'a Expression) -> &'a Expression {
        let parent = guiding_place.get_parent_ref().unwrap();
        if self == parent {
            match guiding_place {
                Expression::BuiltinFuncApp(BuiltinFuncApp {
                    function: BuiltinFunc::Index,
                    arguments,
                    ..
                }) => &arguments[1],
                _ => unreachable!(
                    "self: {} ({}), guiding_place: {}",
                    self,
                    self.get_type(),
                    guiding_place
                ),
            }
        } else {
            self.get_index(parent)
        }
    }

    pub fn none_permission() -> Self {
        Self::constant_no_pos(ConstantValue::Int(0), Type::MPerm)
    }

    pub fn full_permission() -> Self {
        Self::constant_no_pos(ConstantValue::Int(1), Type::MPerm)
    }
}
