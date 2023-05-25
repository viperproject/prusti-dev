use super::{
    super::ast::{
        expression::{
            visitors::{
                default_fold_expression, default_fold_quantifier, default_walk_binary_op,
                default_walk_expression, ExpressionFolder, ExpressionWalker,
            },
            *,
        },
        position::Position,
        predicate::visitors::{PredicateFolder, PredicateWalker},
        ty::{self, visitors::TypeFolder, LifetimeConst, Type},
    },
    ty::Typed,
};
use crate::common::expression::{ExpressionIterator, SyntacticEvaluation, UnaryOperationHelpers};
use std::collections::BTreeMap;

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
            | Expression::AddrOf(AddrOf { box ref base, .. })
            | Expression::EvalIn(EvalIn {
                body: box ref base, ..
            }) => Some(base),
            Expression::LabelledOld(_) => None,
            Expression::BuiltinFuncApp(BuiltinFuncApp {
                function: BuiltinFunc::Index,
                arguments,
                ..
            }) => Some(&arguments[0]),
            expr => unreachable!("{}", expr),
        }
    }
    pub fn get_parent_ref_step_into_old(&self) -> Option<&Expression> {
        if let Expression::LabelledOld(LabelledOld { box ref base, .. }) = self {
            Some(base)
        } else {
            self.get_parent_ref()
        }
    }
    /// Peels only up to functions.
    pub fn get_parent_ref_of_place_like(&self) -> Option<&Expression> {
        match self {
            Expression::Local(_) => None,
            Expression::Variant(Variant { box ref base, .. })
            | Expression::Field(Field { box ref base, .. })
            | Expression::Deref(Deref { box ref base, .. })
            | Expression::AddrOf(AddrOf { box ref base, .. })
            | Expression::EvalIn(EvalIn {
                body: box ref base, ..
            }) => Some(base),
            Expression::LabelledOld(_) => None,
            Expression::BuiltinFuncApp(BuiltinFuncApp {
                function: BuiltinFunc::Index,
                arguments,
                ..
            }) => Some(&arguments[0]),
            Expression::FuncApp(_) => None,
            expr => unreachable!("{}", expr),
        }
    }
    /// Create a new place with the provided parent.
    pub fn with_new_parent(&self, new_parent: Self) -> Self {
        match self {
            Expression::Variant(expression) => Expression::Variant(Variant {
                base: Box::new(new_parent),
                ..expression.clone()
            }),
            Expression::Field(expression) => Expression::Field(Field {
                base: Box::new(new_parent),
                ..expression.clone()
            }),
            Expression::Deref(expression) => Expression::Deref(Deref {
                base: Box::new(new_parent),
                ..expression.clone()
            }),
            Expression::AddrOf(expression) => Expression::AddrOf(AddrOf {
                base: Box::new(new_parent),
                ..expression.clone()
            }),
            _ => unreachable!("Cannot change parent for {}", self),
        }
    }
    /// Only defined for places.
    pub fn try_into_parent(self) -> Option<Self> {
        debug_assert!(self.is_place());
        match self {
            Expression::Local(_) => None,
            Expression::Variant(Variant { box base, .. })
            | Expression::Field(Field { box base, .. })
            | Expression::Deref(Deref { box base, .. })
            | Expression::AddrOf(AddrOf { box base, .. }) => Some(base),
            Expression::LabelledOld(_) => None,
            Expression::BuiltinFuncApp(BuiltinFuncApp {
                function: BuiltinFunc::Index,
                arguments,
                ..
            }) => Some(arguments[0].clone()),
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
            | Expression::LabelledOld(LabelledOld { base, .. })
            | Expression::EvalIn(EvalIn { body: base, .. }) => base.is_place(),
            Expression::BuiltinFuncApp(BuiltinFuncApp {
                function: BuiltinFunc::Index,
                arguments,
                ..
            }) if arguments.len() == 2 => arguments[0].is_place() && arguments[1].is_place(),
            _ => false,
        }
    }
    pub fn collect_all_places(&self) -> Vec<Expression> {
        struct Collector {
            // We use `Vec` instead of `HashSet` to make sure we are
            // deterministic.
            places: Vec<Expression>,
        }
        impl ExpressionWalker for Collector {
            fn walk_expression(&mut self, expression: &Expression) {
                if expression.is_place() {
                    self.places.push(expression.clone());
                } else {
                    default_walk_expression(self, expression)
                }
            }
        }
        let mut collector = Collector { places: Vec::new() };
        collector.walk_expression(self);
        collector.places
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
                    return None;
                }
            }
        }
        None
    }

    pub fn is_deref_of_lifetime(&self, searched_lifetime: &ty::LifetimeConst) -> bool {
        if let Some(parent) = self.get_parent_ref() {
            if self.is_deref() || self.is_field() {
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

    /// Precondition: `self.is_deref_of_lifetime(searched_lifetime)`.
    pub fn into_ref_with_lifetime(self, searched_lifetime: &ty::LifetimeConst) -> Self {
        match self {
            Self::Deref(Deref { base, .. }) | Self::Field(Field { base, .. }) => {
                if let Type::Reference(ty::Reference { lifetime, .. }) = base.get_type() {
                    if searched_lifetime == lifetime {
                        *base
                    } else {
                        base.into_ref_with_lifetime(searched_lifetime)
                    }
                } else {
                    base.into_ref_with_lifetime(searched_lifetime)
                }
            }
            _ => self
                .try_into_parent()
                .unwrap()
                .into_ref_with_lifetime(searched_lifetime),
        }
    }

    /// Check whether the place is a dereference if that is the case, return its
    /// base.
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

    /// Check whether the place is a dereference of a reference and if that is
    /// the case, return its base.
    pub fn get_last_dereferenced_reference(&self) -> Option<&Expression> {
        assert!(self.is_place());
        if let Expression::Deref(Deref { box base, .. }) = self {
            if let Type::Reference(_) = base.get_type() {
                Some(base)
            } else {
                base.get_last_dereferenced_reference()
            }
        } else if let Some(parent) = self.get_parent_ref() {
            parent.get_last_dereferenced_reference()
        } else {
            None
        }
    }

    /// Same as `get_last_dereferenced_reference`, just returns the first
    /// reference.
    pub fn get_first_dereferenced_reference(&self) -> Option<&Expression> {
        assert!(self.is_place());
        if let Expression::Deref(Deref { box base, .. }) = self {
            let parent_ref = base.get_first_dereferenced_reference();
            if parent_ref.is_some() {
                parent_ref
            } else if let Type::Reference(_) = base.get_type() {
                Some(base)
            } else {
                None
            }
        } else if let Some(parent) = self.get_parent_ref() {
            parent.get_first_dereferenced_reference()
        } else {
            None
        }
    }

    pub fn is_behind_pointer_dereference(&self) -> bool {
        if let Some(parent) = self.get_parent_ref_of_place_like() {
            if self.is_deref() && parent.get_type().is_pointer() {
                return true;
            }
            parent.is_behind_pointer_dereference()
        } else {
            false
        }
    }

    pub fn get_last_dereference(&self) -> Option<&Deref> {
        if let Expression::Deref(deref) = self {
            return Some(deref);
        }
        if let Some(parent) = self.get_parent_ref_of_place_like() {
            parent.get_last_dereference()
        } else {
            None
        }
    }

    pub fn get_last_dereferenced_pointer(&self) -> Option<&Expression> {
        assert!(self.is_place());
        if let Some(parent) = self.get_parent_ref() {
            if self.is_deref() && parent.get_type().is_pointer() {
                return Some(parent);
            }
            parent.get_last_dereferenced_pointer()
        } else {
            None
        }
    }

    pub fn get_first_dereferenced_pointer(&self) -> Option<&Expression> {
        assert!(self.is_place());
        if let Some(last_pointer) = self.get_last_dereferenced_pointer() {
            if let Some(parent) = last_pointer.get_first_dereferenced_pointer() {
                Some(parent)
            } else {
                Some(last_pointer)
            }
        } else {
            None
        }
    }

    pub fn get_deref_uniqueness(&self) -> Option<ty::Uniqueness> {
        assert!(self.is_place());
        if let Some(parent) = self.get_parent_ref() {
            let parent_uniqueness = parent.get_deref_uniqueness();
            if self.is_deref() {
                if let Type::Reference(ty::Reference { uniqueness, .. }) = parent.get_type() {
                    if let Some(parent_uniqueness) = parent_uniqueness {
                        if parent_uniqueness == ty::Uniqueness::Shared {
                            return Some(parent_uniqueness);
                        }
                    }
                    return Some(*uniqueness);
                }
            }
            parent_uniqueness
        } else {
            None
        }
    }

    pub fn get_last_old_label(&self) -> Option<&Expression> {
        assert!(self.is_place());
        if self.is_labelled_old() {
            return Some(self);
        }
        if let Some(parent) = self.get_parent_ref() {
            parent.get_last_old_label()
        } else {
            None
        }
    }

    pub fn get_first_old_label(&self) -> Option<&Expression> {
        assert!(self.is_place());
        if let Some(last_old) = self.get_last_old_label() {
            if let Some(parent) = last_old.get_parent_ref() {
                if let Some(first_old) = parent.get_first_old_label() {
                    Some(first_old)
                } else {
                    Some(last_old)
                }
            } else {
                Some(last_old)
            }
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

    pub fn check_no_erased_lifetime(&self) {
        struct LifetimeChecker {}
        impl ExpressionWalker for LifetimeChecker {
            fn walk_type(&mut self, ty: &Type) {
                ty.check_no_erased_lifetime();
            }
            fn walk_variable_decl(&mut self, variable_decl: &VariableDecl) {
                variable_decl.ty.check_no_erased_lifetime();
            }
            fn walk_field_decl(&mut self, field_decl: &FieldDecl) {
                field_decl.ty.check_no_erased_lifetime();
            }
        }
        LifetimeChecker {}.walk_expression(self);
    }

    #[must_use]
    pub fn replace_lifetimes(
        self,
        lifetime_replacement_map: &BTreeMap<LifetimeConst, LifetimeConst>,
    ) -> Self {
        struct Replacer<'a> {
            lifetime_replacement_map: &'a BTreeMap<LifetimeConst, LifetimeConst>,
        }
        impl<'a> ExpressionFolder for Replacer<'a> {
            fn fold_type(&mut self, ty: Type) -> Type {
                ty.replace_lifetimes(self.lifetime_replacement_map)
            }
            fn fold_variable_decl(&mut self, variable_decl: VariableDecl) -> VariableDecl {
                VariableDecl {
                    name: variable_decl.name,
                    ty: variable_decl
                        .ty
                        .replace_lifetimes(self.lifetime_replacement_map),
                }
            }
            fn fold_field_decl(&mut self, field_decl: FieldDecl) -> FieldDecl {
                // FIXME: Fix the visitor generator to follow relative imports
                // when generating visitors.
                FieldDecl {
                    ty: field_decl
                        .ty
                        .replace_lifetimes(self.lifetime_replacement_map),
                    ..field_decl
                }
            }
        }
        Replacer {
            lifetime_replacement_map,
        }
        .fold_expression(self)
    }

    #[must_use]
    pub fn replace_lifetime(
        self,
        old_lifetime: &LifetimeConst,
        new_lifetime: &LifetimeConst,
    ) -> Self {
        struct Replacer<'a> {
            old_lifetime: &'a LifetimeConst,
            new_lifetime: &'a LifetimeConst,
        }
        impl<'a> ExpressionFolder for Replacer<'a> {
            fn fold_type(&mut self, ty: Type) -> Type {
                ty.replace_lifetime(self.old_lifetime, self.new_lifetime)
            }
            fn fold_variable_decl(&mut self, variable_decl: VariableDecl) -> VariableDecl {
                VariableDecl {
                    name: variable_decl.name,
                    ty: variable_decl
                        .ty
                        .replace_lifetime(self.old_lifetime, self.new_lifetime),
                }
            }
            fn fold_field_decl(&mut self, field_decl: FieldDecl) -> FieldDecl {
                // FIXME: Fix the visitor generator to follow relative imports
                // when generating visitors.
                FieldDecl {
                    ty: field_decl
                        .ty
                        .replace_lifetime(self.old_lifetime, self.new_lifetime),
                    ..field_decl
                }
            }
        }
        Replacer {
            old_lifetime,
            new_lifetime,
        }
        .fold_expression(self)
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
            fn fold_predicate(&mut self, predicate: Predicate) -> Predicate {
                PredicateFolder::fold_predicate(self, predicate)
            }
            fn fold_trigger(&mut self, trigger: Trigger) -> Trigger {
                Trigger::new(
                    trigger
                        .terms
                        .into_iter()
                        .map(|term| ExpressionFolder::fold_expression(self, term))
                        .collect::<Vec<_>>(),
                )
            }
        }
        impl<'a> PredicateFolder for PlaceReplacer<'a> {
            fn fold_expression(&mut self, expression: Expression) -> Expression {
                ExpressionFolder::fold_expression(self, expression)
            }
        }
        let mut replacer = PlaceReplacer {
            target,
            replacement,
        };
        ExpressionFolder::fold_expression(&mut replacer, self)
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

            fn fold_predicate(&mut self, predicate: Predicate) -> Predicate {
                PredicateFolder::fold_predicate(self, predicate)
            }

            fn fold_trigger(&mut self, trigger: Trigger) -> Trigger {
                Trigger::new(
                    trigger
                        .terms
                        .into_iter()
                        .map(|term| ExpressionFolder::fold_expression(self, term))
                        .collect::<Vec<_>>(),
                )
            }
        }
        impl<'a> PredicateFolder for PlaceReplacer<'a> {
            fn fold_expression(&mut self, expression: Expression) -> Expression {
                ExpressionFolder::fold_expression(self, expression)
            }
        }
        let mut replacer = PlaceReplacer { replacements };
        ExpressionFolder::fold_expression(&mut replacer, self)
    }
    #[must_use]
    pub fn replace_self(self, replacement: &Expression) -> Self {
        struct PlaceReplacer<'a> {
            replacement: &'a Expression,
        }
        impl<'a> ExpressionFolder for PlaceReplacer<'a> {
            fn fold_local_enum(&mut self, local: Local) -> Expression {
                if local.variable.is_self_variable() {
                    assert_eq!(
                        &local.variable.ty,
                        self.replacement.get_type(),
                        "{} → {}",
                        local.variable.ty,
                        self.replacement
                    );
                    self.replacement.clone()
                } else {
                    Expression::Local(local)
                }
            }
            fn fold_predicate(&mut self, predicate: Predicate) -> Predicate {
                PredicateFolder::fold_predicate(self, predicate)
            }

            fn fold_trigger(&mut self, trigger: Trigger) -> Trigger {
                Trigger::new(
                    trigger
                        .terms
                        .into_iter()
                        .map(|term| ExpressionFolder::fold_expression(self, term))
                        .collect::<Vec<_>>(),
                )
            }
        }
        impl<'a> PredicateFolder for PlaceReplacer<'a> {
            fn fold_expression(&mut self, expression: Expression) -> Expression {
                ExpressionFolder::fold_expression(self, expression)
            }
        }
        let mut replacer = PlaceReplacer { replacement };
        ExpressionFolder::fold_expression(&mut replacer, self)
    }
    pub fn peel_unfoldings(&self) -> &Self {
        match self {
            Expression::Unfolding(unfolding) => unfolding.body.peel_unfoldings(),
            _ => self,
        }
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
    /// Simplify `construtor(arg1, arg2, ..., argn).field_k` to `argk`.
    pub fn simplify_out_constructors(self) -> Self {
        struct Simplifier;
        impl ExpressionFolder for Simplifier {
            fn fold_expression(&mut self, expression: Expression) -> Expression {
                match expression {
                    Expression::Field(Field {
                        base: box Expression::Constructor(constructor),
                        field,
                        position: _,
                    }) => ExpressionFolder::fold_expression(
                        self,
                        constructor.arguments[field.index].clone(),
                    ),
                    _ => default_fold_expression(self, expression),
                }
            }
            fn fold_predicate(&mut self, predicate: Predicate) -> Predicate {
                PredicateFolder::fold_predicate(self, predicate)
            }
            fn fold_trigger(&mut self, trigger: Trigger) -> Trigger {
                Trigger::new(
                    trigger
                        .terms
                        .into_iter()
                        .map(|term| ExpressionFolder::fold_expression(self, term))
                        .collect::<Vec<_>>(),
                )
            }
        }
        impl PredicateFolder for Simplifier {
            fn fold_expression(&mut self, expression: Expression) -> Expression {
                ExpressionFolder::fold_expression(self, expression)
            }
        }
        ExpressionFolder::fold_expression(&mut Simplifier, self)
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
                Expression::BinaryOp(BinaryOp {
                    op_kind: BinaryOpKind::Add,
                    left:
                        box Expression::BuiltinFuncApp(BuiltinFuncApp {
                            function: BuiltinFunc::NewInt,
                            arguments,
                            ..
                        }),
                    right,
                    ..
                }) if arguments[0].is_zero() => *right,
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
            fn fold_predicate(&mut self, predicate: Predicate) -> Predicate {
                PredicateFolder::fold_predicate(self, predicate)
            }
            fn fold_trigger(&mut self, trigger: Trigger) -> Trigger {
                Trigger::new(
                    trigger
                        .terms
                        .into_iter()
                        .map(|term| ExpressionFolder::fold_expression(self, term))
                        .collect::<Vec<_>>(),
                )
            }
        }
        impl PredicateFolder for Simplifier {
            fn fold_expression(&mut self, expression: Expression) -> Expression {
                ExpressionFolder::fold_expression(self, expression)
            }
        }
        ExpressionFolder::fold_expression(&mut Simplifier, self)
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
            fn walk_predicate(&mut self, predicate: &Predicate) {
                PredicateWalker::walk_predicate(self, predicate)
            }
            fn walk_trigger(&mut self, trigger: &Trigger) {
                for term in &trigger.terms {
                    ExpressionWalker::walk_expression(self, term)
                }
            }
        }
        impl<'a> PredicateWalker for ExprFinder<'a> {
            fn walk_expression(&mut self, expr: &Expression) {
                ExpressionWalker::walk_expression(self, expr)
            }
        }

        let mut finder = ExprFinder {
            sub_target,
            found: false,
        };
        ExpressionWalker::walk_expression(&mut finder, self);
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
    pub fn has_prefix_with_lifetimes(&self, potential_prefix: &Expression) -> bool {
        if self == potential_prefix {
            true
        } else {
            self.get_parent_ref()
                .map(|parent| parent.has_prefix_with_lifetimes(potential_prefix))
                .unwrap_or(false)
        }
    }
    /// Note: this function ignores lifetimes.
    pub fn has_prefix(&self, potential_prefix: &Expression) -> bool {
        // FIXME: Avoid clone.
        self.clone()
            .erase_lifetime()
            .has_prefix_with_lifetimes(&potential_prefix.clone().erase_lifetime())
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

    pub fn is_pure(&self) -> bool {
        struct Checker {
            is_pure: bool,
        }
        impl ExpressionWalker for Checker {
            fn walk_acc_predicate(&mut self, _: &AccPredicate) {
                self.is_pure = false;
            }
            fn walk_eval_in(&mut self, eval_in: &EvalIn) {
                self.walk_expression(&eval_in.body);
            }
        }
        let mut checker = Checker { is_pure: true };
        checker.walk_expression(self);
        checker.is_pure
    }
}

/// Methods for collecting places.
impl Expression {
    /// Returns place used in `own`.
    pub fn collect_owned_places(&self) -> (Vec<Expression>, Vec<Expression>) {
        struct Collector {
            owned_places: Vec<Expression>,
            owned_range_addresses: Vec<Expression>,
        }
        impl<'a> ExpressionWalker for Collector {
            fn walk_acc_predicate(&mut self, acc_predicate: &AccPredicate) {
                match &*acc_predicate.predicate {
                    Predicate::LifetimeToken(_)
                    | Predicate::MemoryBlockStack(_)
                    | Predicate::MemoryBlockStackDrop(_)
                    | Predicate::MemoryBlockHeap(_)
                    | Predicate::MemoryBlockHeapRange(_)
                    | Predicate::MemoryBlockHeapDrop(_) => {}
                    Predicate::OwnedNonAliased(predicate) => {
                        self.owned_places.push(predicate.place.clone());
                    }
                    Predicate::OwnedRange(predicate) => {
                        self.owned_range_addresses.push(predicate.address.clone());
                    }
                    Predicate::OwnedSet(predicate) => {
                        unimplemented!("predicate: {}", predicate);
                    }
                    Predicate::UniqueRef(predicate) => {
                        self.owned_places.push(predicate.place.clone());
                    }
                    Predicate::UniqueRefRange(predicate) => {
                        self.owned_range_addresses.push(predicate.address.clone());
                    }
                    Predicate::FracRef(predicate) => {
                        self.owned_places.push(predicate.place.clone());
                    }
                    Predicate::FracRefRange(predicate) => {
                        self.owned_range_addresses.push(predicate.address.clone());
                    }
                }
            }
        }
        let mut collector = Collector {
            owned_places: Vec::new(),
            owned_range_addresses: Vec::new(),
        };
        collector.walk_expression(self);
        (collector.owned_places, collector.owned_range_addresses)
    }

    /// Returns places used in `own` with path conditions that guard them.
    pub fn collect_guarded_owned_places(&self) -> Vec<(Expression, Expression)> {
        struct Collector {
            path_condition: Vec<Expression>,
            owned_places: Vec<(Expression, Expression)>,
        }
        impl<'a> ExpressionWalker for Collector {
            fn walk_acc_predicate(&mut self, acc_predicate: &AccPredicate) {
                match &*acc_predicate.predicate {
                    Predicate::LifetimeToken(_)
                    | Predicate::MemoryBlockStack(_)
                    | Predicate::MemoryBlockStackDrop(_)
                    | Predicate::MemoryBlockHeap(_)
                    | Predicate::MemoryBlockHeapRange(_)
                    | Predicate::MemoryBlockHeapDrop(_) => {}
                    Predicate::OwnedNonAliased(predicate) => {
                        self.owned_places.push((
                            self.path_condition.iter().cloned().conjoin(),
                            predicate.place.clone(),
                        ));
                    }
                    Predicate::OwnedRange(predicate) => {
                        unimplemented!("predicate: {}", predicate);
                    }
                    Predicate::OwnedSet(predicate) => {
                        unimplemented!("predicate: {}", predicate);
                    }
                    Predicate::UniqueRef(predicate) => {
                        self.owned_places.push((
                            self.path_condition.iter().cloned().conjoin(),
                            predicate.place.clone(),
                        ));
                    }
                    Predicate::UniqueRefRange(predicate) => {
                        unimplemented!("predicate: {}", predicate);
                    }
                    Predicate::FracRef(predicate) => {
                        self.owned_places.push((
                            self.path_condition.iter().cloned().conjoin(),
                            predicate.place.clone(),
                        ));
                    }
                    Predicate::FracRefRange(predicate) => {
                        unimplemented!("predicate: {}", predicate);
                    }
                }
            }
            fn walk_binary_op(&mut self, binary_op: &BinaryOp) {
                if binary_op.op_kind == BinaryOpKind::Implies {
                    self.path_condition.push((*binary_op.left).clone());
                    self.walk_expression(&binary_op.right);
                    self.path_condition.pop();
                } else {
                    default_walk_binary_op(self, binary_op);
                }
            }
            fn walk_conditional(&mut self, conditional: &Conditional) {
                self.path_condition.push((*conditional.guard).clone());
                self.walk_expression(&conditional.then_expr);
                let guard = self.path_condition.pop().unwrap();
                self.path_condition.push(Expression::not(guard));
                self.walk_expression(&conditional.else_expr);
                self.path_condition.pop();
            }
        }
        let mut collector = Collector {
            path_condition: Vec::new(),
            owned_places: Vec::new(),
        };
        collector.walk_expression(self);
        collector.owned_places
    }

    /// Returns the expression with all pure parts removed and implications
    /// converted into conditionals.
    ///
    /// This method is different from `collect_guarded_owned_places` in that it
    /// still returns a single expression preserving most of the original
    /// structure.
    pub fn convert_into_permission_expression(self) -> Expression {
        struct Remover {}
        impl<'a> ExpressionFolder for Remover {
            fn fold_expression(&mut self, expression: Expression) -> Expression {
                if expression.is_pure() {
                    true.into()
                } else {
                    default_fold_expression(self, expression)
                }
            }
            fn fold_binary_op_enum(&mut self, binary_op: BinaryOp) -> Expression {
                if binary_op.op_kind == BinaryOpKind::Implies {
                    let guard = *binary_op.left;
                    let then_expr = self.fold_expression(*binary_op.right);
                    let else_expr = false.into();
                    Expression::conditional(guard, then_expr, else_expr, binary_op.position)
                } else {
                    Expression::BinaryOp(self.fold_binary_op(binary_op))
                }
            }
        }
        let mut remover = Remover {};
        remover.fold_expression(self)
    }

    /// Returns places that contain dereferences with their path conditions.
    pub fn collect_guarded_dereferenced_places(&self) -> Vec<(Expression, Expression)> {
        struct Collector {
            path_condition: Vec<Expression>,
            deref_places: Vec<(Expression, Expression)>,
        }
        impl<'a> ExpressionWalker for Collector {
            fn walk_expression(&mut self, expression: &Expression) {
                if expression.is_place() {
                    if expression.get_last_dereferenced_pointer().is_some() {
                        self.deref_places.push((
                            self.path_condition.iter().cloned().conjoin(),
                            expression.clone(),
                        ));
                    }
                } else {
                    default_walk_expression(self, expression)
                }
            }
            fn walk_binary_op(&mut self, binary_op: &BinaryOp) {
                if binary_op.op_kind == BinaryOpKind::Implies {
                    self.walk_expression(&binary_op.left);
                    self.path_condition.push((*binary_op.left).clone());
                    self.walk_expression(&binary_op.right);
                    self.path_condition.pop();
                } else {
                    default_walk_binary_op(self, binary_op);
                }
            }
            fn walk_conditional(&mut self, conditional: &Conditional) {
                self.walk_expression(&conditional.guard);
                self.path_condition.push((*conditional.guard).clone());
                self.walk_expression(&conditional.then_expr);
                let guard = self.path_condition.pop().unwrap();
                self.path_condition.push(Expression::not(guard));
                self.walk_expression(&conditional.else_expr);
                self.path_condition.pop();
            }
        }
        let mut collector = Collector {
            path_condition: Vec::new(),
            deref_places: Vec::new(),
        };
        collector.walk_expression(self);
        collector.deref_places
    }
}
