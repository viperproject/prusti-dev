use super::ty::Typed;
use crate::{
    common::{expression::SyntacticEvaluation, position::Positioned},
    gen::low::expression::visitors::default_fold_predicate_access_predicate,
    low::ast::expression::{
        visitors::{
            default_fold_expression, default_fold_labelled_old, ExpressionFolder, ExpressionWalker,
        },
        *,
    },
};
use rustc_hash::FxHashMap;

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
            | BinaryOpKind::Mod => argument_type,
        }
    }
}

impl Expression {
    pub fn function_call<S: Into<String>>(
        name: S,
        arguments: Vec<Expression>,
        return_type: Type,
    ) -> Expression {
        let parameters = arguments
            .iter()
            .enumerate()
            .map(|(i, argument)| VariableDecl {
                name: format!("_{i}"),
                ty: argument.get_type().clone(),
            })
            .collect();
        Expression::func_app_no_pos(name.into(), arguments, parameters, return_type)
    }
    pub fn domain_function_call(
        domain_name: impl ToString,
        function_name: impl ToString,
        arguments: Vec<Expression>,
        return_type: Type,
    ) -> Expression {
        let parameters = arguments
            .iter()
            .enumerate()
            .map(|(i, argument)| VariableDecl {
                name: format!("_{i}"),
                ty: argument.get_type().clone(),
            })
            .collect();
        Expression::domain_func_app_no_pos(
            domain_name.to_string(),
            function_name.to_string(),
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
    pub fn is_place(&self) -> bool {
        match self {
            Expression::Local(_) => true,
            Expression::Field(Field { base, .. })
            | Expression::LabelledOld(LabelledOld { base, .. }) => base.is_place(),
            _ => false,
        }
    }
    #[must_use]
    pub fn replace_place(self, target: &Expression, replacement: &Expression) -> Self {
        debug_assert!(target.is_place());
        assert_eq!(
            target.get_type(),
            replacement.get_type(),
            "{target} → {replacement}"
        );
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
            fn fold_trigger(&mut self, mut trigger: Trigger) -> Trigger {
                for term in std::mem::take(&mut trigger.terms) {
                    trigger.terms.push(self.fold_expression(term));
                }
                trigger
            }
        }
        let mut replacer = PlaceReplacer {
            target,
            replacement,
        };
        replacer.fold_expression(self)
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
        }
        let mut replacer = PlaceReplacer { replacement };
        replacer.fold_expression(self)
    }
    #[must_use]
    pub fn substitute_variables(
        self,
        replacements: &FxHashMap<&VariableDecl, &Expression>,
    ) -> Self {
        struct PlaceReplacer<'a> {
            replacements: &'a FxHashMap<&'a VariableDecl, &'a Expression>,
        }
        impl<'a> ExpressionFolder for PlaceReplacer<'a> {
            fn fold_local_enum(&mut self, local: Local) -> Expression {
                if let Some(&expression) = self.replacements.get(&local.variable) {
                    expression.clone()
                } else {
                    Expression::Local(local)
                }
            }
            fn fold_trigger(&mut self, trigger: Trigger) -> Trigger {
                Trigger {
                    terms: trigger
                        .terms
                        .into_iter()
                        .map(|expression| self.fold_expression(expression))
                        .collect(),
                }
            }
        }
        PlaceReplacer { replacements }.fold_expression(self)
    }
    #[must_use]
    pub fn map_variables<F: FnMut(VariableDecl) -> VariableDecl>(self, map: F) -> Self {
        struct PlaceReplacer<F: FnMut(VariableDecl) -> VariableDecl> {
            map: F,
        }
        impl<F: FnMut(VariableDecl) -> VariableDecl> ExpressionFolder for PlaceReplacer<F> {
            fn fold_local(&mut self, mut local: Local) -> Local {
                local.variable = (self.map)(local.variable);
                local
            }
            fn fold_trigger(&mut self, trigger: Trigger) -> Trigger {
                Trigger {
                    terms: trigger
                        .terms
                        .into_iter()
                        .map(|expression| self.fold_expression(expression))
                        .collect(),
                }
            }
        }
        PlaceReplacer { map }.fold_expression(self)
    }
    #[must_use]
    pub fn replace_predicate_permissions(self, new_predicate_permission: &Box<Expression>) -> Self {
        struct PermissionReplacer<'a> {
            new_predicate_permission: &'a Box<Expression>,
        }
        impl<'a> ExpressionFolder for PermissionReplacer<'a> {
            fn fold_predicate_access_predicate(
                &mut self,
                predicate: PredicateAccessPredicate,
            ) -> PredicateAccessPredicate {
                let mut new_predicate = default_fold_predicate_access_predicate(self, predicate);
                assert!(
                    new_predicate.permission.is_full_permission(),
                    "must have full permission: {new_predicate}"
                );
                new_predicate.permission = self.new_predicate_permission.clone();
                new_predicate
            }
        }
        PermissionReplacer {
            new_predicate_permission,
        }
        .fold_expression(self)
    }
    #[must_use]
    pub fn replace_subexpressions(self, replacements: &FxHashMap<Expression, Expression>) -> Self {
        struct SubexpressionReplacer<'a> {
            replacements: &'a FxHashMap<Expression, Expression>,
        }
        impl<'a> ExpressionFolder for SubexpressionReplacer<'a> {
            fn fold_expression(&mut self, expression: Expression) -> Expression {
                if let Some(replacement) = self.replacements.get(&expression) {
                    replacement.clone()
                } else {
                    default_fold_expression(self, expression)
                }
            }
            fn fold_trigger(&mut self, trigger: Trigger) -> Trigger {
                Trigger {
                    terms: trigger
                        .terms
                        .into_iter()
                        .map(|expression| self.fold_expression(expression))
                        .collect(),
                }
            }
        }
        let mut replacer = SubexpressionReplacer { replacements };
        replacer.fold_expression(self)
    }
    /// Wraps all heap-dependent expressions (currently we have only function
    /// calls that depend on the heap) in `old`.
    pub fn wrap_in_old(self, old_label: &str) -> Self {
        struct Wrapper<'a> {
            old_label: &'a str,
        }
        impl<'a> ExpressionFolder for Wrapper<'a> {
            fn fold_labelled_old(&mut self, labelled_old: LabelledOld) -> LabelledOld {
                labelled_old
            }
            fn fold_func_app_enum(&mut self, func_app: FuncApp) -> Expression {
                let position = func_app.position;
                Expression::labelled_old(
                    Some(self.old_label.to_string()),
                    Expression::FuncApp(func_app),
                    position,
                )
            }
            fn fold_trigger(&mut self, mut trigger: Trigger) -> Trigger {
                for term in std::mem::take(&mut trigger.terms) {
                    trigger.terms.push(self.fold_expression(term));
                }
                trigger
            }
        }
        let mut wrapper = Wrapper { old_label };
        wrapper.fold_expression(self)
        // let wrapper = |expression: Expression| {
        //     let position = expression.position();
        //     assert!(expression.is_pure(), "{expression}");
        //     Expression::labelled_old(Some(old_label.to_string()), expression, position)
        // };
        // match self {
        //     Expression::LabelledOld(expression) => Expression::LabelledOld(expression),
        //     Expression::PredicateAccessPredicate(mut expression) => {
        //         expression.arguments = expression
        //             .arguments
        //             .into_iter()
        //             .map(|arg| arg.wrap_in_old(old_label))
        //             .collect();
        //         Expression::PredicateAccessPredicate(expression)
        //     }
        //     Expression::FieldAccessPredicate(_expression) => {
        //         unimplemented!();
        //     }
        //     Expression::BinaryOp(expression) => match expression.op_kind {
        //         BinaryOpKind::And => {
        //             let left = expression.left.wrap_in_old(old_label);
        //             let right = expression.right.wrap_in_old(old_label);
        //             Expression::binary_op(BinaryOpKind::And, left, right, expression.position)
        //         }
        //         BinaryOpKind::Implies => {
        //             let left = wrapper(*expression.left);
        //             let right = expression.right.wrap_in_old(old_label);
        //             Expression::binary_op(BinaryOpKind::Implies, left, right, expression.position)
        //         }
        //         _ => wrapper(Expression::BinaryOp(expression)),
        //     },
        //     Expression::Quantifier(mut expression) if !expression.body.is_pure() => {
        //         for mut trigger in std::mem::take(&mut expression.triggers) {
        //             for term in std::mem::take(&mut trigger.terms) {
        //                 trigger.terms.push(term.wrap_in_old(old_label));
        //             }
        //             expression.triggers.push(trigger);
        //         }
        //         let body = expression.body.wrap_in_old(old_label);
        //         Expression::Quantifier(Quantifier {
        //             body: Box::new(body),
        //             ..expression
        //         })
        //     }
        //     _ => wrapper(self),
        // }
    }
    #[must_use]
    pub fn set_old_label(self, old_label: &str) -> Self {
        struct LabelReplacer<'a> {
            old_label: &'a str,
        }
        impl<'a> ExpressionFolder for LabelReplacer<'a> {
            fn fold_labelled_old(&mut self, labelled_old: LabelledOld) -> LabelledOld {
                let mut labelled_old = default_fold_labelled_old(self, labelled_old);
                if labelled_old.label.is_none() {
                    labelled_old.label = Some(self.old_label.to_string());
                }
                labelled_old
            }
            fn fold_trigger(&mut self, mut trigger: Trigger) -> Trigger {
                for term in std::mem::take(&mut trigger.terms) {
                    trigger.terms.push(self.fold_expression(term));
                }
                trigger
            }
        }
        LabelReplacer { old_label }.fold_expression(self)
    }
    pub fn remove_unnecessary_old(self) -> Self {
        struct OldRemover;
        impl ExpressionFolder for OldRemover {
            fn fold_labelled_old_enum(&mut self, labelled_old: LabelledOld) -> Expression {
                let labelled_old = default_fold_labelled_old(self, labelled_old);
                if labelled_old.base.is_heap_independent() {
                    *labelled_old.base
                } else {
                    Expression::LabelledOld(labelled_old)
                }
            }
        }
        OldRemover.fold_expression(self)
    }
    pub fn remove_old_label(self, label: &str) -> Self {
        struct OldRemover<'a> {
            label: &'a str,
        }
        impl<'a> ExpressionFolder for OldRemover<'a> {
            fn fold_labelled_old_enum(&mut self, labelled_old: LabelledOld) -> Expression {
                let labelled_old = default_fold_labelled_old(self, labelled_old);
                if labelled_old.label.as_deref() == Some(self.label) {
                    *labelled_old.base
                } else {
                    Expression::LabelledOld(labelled_old)
                }
            }
        }
        let mut remover = OldRemover { label };
        remover.fold_expression(self)
    }
    #[must_use]
    pub fn replace_discriminant(self, new_discriminant: &Expression) -> Self {
        struct DiscriminantReplacer<'a> {
            new_discriminant: &'a Expression,
        }
        impl<'a> ExpressionFolder for DiscriminantReplacer<'a> {
            fn fold_expression(&mut self, expression: Expression) -> Expression {
                if expression.is_discriminant() {
                    self.new_discriminant.clone()
                } else {
                    default_fold_expression(self, expression)
                }
            }
        }
        let mut replacer = DiscriminantReplacer { new_discriminant };
        replacer.fold_expression(self)
    }
    pub fn full_permission() -> Self {
        Self::constant_no_pos(1.into(), Type::Perm)
    }
    pub fn is_full_permission(&self) -> bool {
        match self {
            Expression::Constant(Constant {
                value: ConstantValue::Int(value),
                ty,
                ..
            }) if ty.is_perm() => *value == 1,
            _ => false,
        }
    }
    pub fn no_permission() -> Self {
        Self::constant_no_pos(0.into(), Type::Perm)
    }
    pub fn is_no_permission(&self) -> bool {
        match self {
            Expression::Constant(Constant {
                value: ConstantValue::Int(value),
                ty,
                ..
            }) if ty.is_perm() => *value == 0,
            _ => false,
        }
    }
    pub fn wildcard_permission() -> Self {
        Self::constant_no_pos((-1i64).into(), Type::Perm)
    }
    pub fn simplify_perm(self) -> Self {
        match self {
            Expression::PermBinaryOp(mut operation) => match operation.op_kind {
                PermBinaryOpKind::Add => match *operation.left {
                    Expression::PermBinaryOp(left_operation) => {
                        if left_operation.right == operation.right
                            && left_operation.op_kind == PermBinaryOpKind::Sub
                        {
                            *left_operation.left
                        } else {
                            operation.left = Box::new(Expression::PermBinaryOp(left_operation));
                            Expression::PermBinaryOp(operation)
                        }
                    }
                    _ => match (*operation.left, *operation.right) {
                        (
                            Expression::Constant(Constant {
                                value: ConstantValue::Int(left_value),
                                ty,
                                position,
                            }),
                            Expression::Constant(Constant {
                                value: ConstantValue::Int(right_value),
                                ..
                            }),
                        ) => {
                            let new_value = left_value + right_value;
                            Self::constant(new_value.into(), ty, position)
                        }
                        (left, right) => unreachable!("{left} + {right}"),
                    },
                },
                PermBinaryOpKind::Sub => {
                    if operation.left == operation.right {
                        Self::no_permission()
                    } else if operation.left.is_constant() && operation.right.is_constant() {
                        match (*operation.left, *operation.right) {
                            (
                                Expression::Constant(Constant {
                                    value: ConstantValue::Int(left_value),
                                    ty,
                                    position,
                                }),
                                Expression::Constant(Constant {
                                    value: ConstantValue::Int(right_value),
                                    ..
                                }),
                            ) => {
                                let new_value = left_value - right_value;
                                Self::constant(new_value.into(), ty, position)
                            }
                            (left, right) => unreachable!("{left} + {right}"),
                        }
                    } else {
                        match *operation.left {
                            Expression::PermBinaryOp(left_operation) => {
                                if left_operation.right == operation.right
                                    && left_operation.op_kind == PermBinaryOpKind::Add
                                {
                                    *left_operation.left
                                } else {
                                    operation.left =
                                        Box::new(Expression::PermBinaryOp(left_operation));
                                    Expression::PermBinaryOp(operation)
                                }
                            }
                            _ => Expression::PermBinaryOp(operation),
                        }
                    }
                }
                PermBinaryOpKind::Mul => unreachable!(),
                PermBinaryOpKind::Div => Expression::PermBinaryOp(operation),
            },
            _ => unreachable!("{self}"),
        }
    }
    pub fn fractional_permission(denominator: u32) -> Self {
        Self::perm_binary_op_no_pos(
            PermBinaryOpKind::Div,
            Self::full_permission(),
            denominator.into(),
        )
    }
    pub fn into_unfolding(self, base: Self) -> Self {
        let predicate = self.unwrap_predicate_access_predicate();
        // Self::unfolding(predicate.name, predicate.arguments, *predicate.permission, base, predicate.position)
        let position = predicate.position;
        Self::unfolding(predicate, base, position)
    }
    pub fn is_pure(&self) -> bool {
        struct Checker {
            is_pure: bool,
        }
        impl ExpressionWalker for Checker {
            fn walk_predicate_access_predicate(&mut self, _: &PredicateAccessPredicate) {
                self.is_pure = false;
            }
            fn walk_field_access_predicate(&mut self, _: &FieldAccessPredicate) {
                self.is_pure = false;
            }
        }
        let mut checker = Checker { is_pure: true };
        checker.walk_expression(self);
        checker.is_pure
    }
    pub fn is_heap_independent(&self) -> bool {
        struct Checker {
            is_heap_independent: bool,
        }
        impl ExpressionWalker for Checker {
            fn walk_predicate_access_predicate(&mut self, _: &PredicateAccessPredicate) {
                self.is_heap_independent = false;
            }
            fn walk_field_access_predicate(&mut self, _: &FieldAccessPredicate) {
                self.is_heap_independent = false;
            }
            fn walk_func_app(&mut self, _: &FuncApp) {
                self.is_heap_independent = false;
            }
        }
        let mut checker = Checker {
            is_heap_independent: true,
        };
        checker.walk_expression(self);
        checker.is_heap_independent
    }
    /// A term is an expression composed of heap-independent function calls and
    /// constants.
    pub fn is_term(&self) -> bool {
        struct Checker {
            is_term: bool,
        }
        impl ExpressionWalker for Checker {
            fn walk_predicate_access_predicate(&mut self, _: &PredicateAccessPredicate) {
                self.is_term = false;
            }
            fn walk_field_access_predicate(&mut self, _: &FieldAccessPredicate) {
                self.is_term = false;
            }
            fn walk_func_app(&mut self, _: &FuncApp) {
                self.is_term = false;
            }
            fn walk_conditional(&mut self, _: &Conditional) {
                self.is_term = false;
            }
            fn walk_quantifier(&mut self, _: &Quantifier) {
                self.is_term = false;
            }
            fn walk_let_expr(&mut self, _: &LetExpr) {
                self.is_term = false;
            }
        }
        let mut checker = Checker { is_term: true };
        checker.walk_expression(self);
        checker.is_term
    }
    pub fn collect_access_predicate_names(&self) -> Vec<String> {
        struct Collector {
            predicate_names: Vec<String>,
        }
        impl ExpressionWalker for Collector {
            fn walk_predicate_access_predicate(&mut self, predicate: &PredicateAccessPredicate) {
                self.predicate_names.push(predicate.name.clone());
            }
        }
        let mut collector = Collector {
            predicate_names: Vec::new(),
        };
        collector.walk_expression(self);
        collector.predicate_names
    }
    fn apply_simplification_rules(self) -> Self {
        let mut expression = self;
        loop {
            expression = match expression {
                Expression::PermBinaryOp(PermBinaryOp {
                    op_kind: PermBinaryOpKind::Add,
                    left,
                    right,
                    position: _,
                }) if left.is_zero() => *right,
                Expression::PermBinaryOp(PermBinaryOp {
                    op_kind: PermBinaryOpKind::Add,
                    left,
                    right,
                    position: _,
                }) if right.is_zero() => *left,
                Expression::PermBinaryOp(PermBinaryOp {
                    op_kind: PermBinaryOpKind::Add,
                    left:
                        box Expression::Constant(Constant {
                            value: ConstantValue::Int(left_value),
                            ty: left_type,
                            ..
                        }),
                    right:
                        box Expression::Constant(Constant {
                            value: ConstantValue::Int(right_value),
                            ty: right_type,
                            ..
                        }),
                    position,
                }) => {
                    assert_eq!(left_type, right_type);
                    Expression::constant(
                        (left_value.checked_add(right_value).unwrap()).into(),
                        left_type.clone(),
                        position,
                    )
                }
                Expression::PermBinaryOp(PermBinaryOp {
                    op_kind: PermBinaryOpKind::Sub,
                    left:
                        box Expression::Constant(Constant {
                            value: ConstantValue::Int(left_value),
                            ty: left_type,
                            ..
                        }),
                    right:
                        box Expression::Constant(Constant {
                            value: ConstantValue::Int(right_value),
                            ty: right_type,
                            ..
                        }),
                    position,
                }) => {
                    assert_eq!(left_type, right_type);
                    Expression::constant(
                        (left_value.checked_sub(right_value).unwrap()).into(),
                        left_type.clone(),
                        position,
                    )
                }
                Expression::Conditional(Conditional {
                    guard: _,
                    then_expr,
                    else_expr,
                    position: _,
                }) if then_expr == else_expr => *then_expr,
                Expression::Conditional(Conditional {
                    guard,
                    then_expr,
                    else_expr: _,
                    position: _,
                }) if guard.is_true() => *then_expr,
                Expression::BinaryOp(BinaryOp {
                    op_kind: BinaryOpKind::EqCmp,
                    left,
                    right,
                    position,
                }) if left == right => Expression::constant(true.into(), Type::Bool, position),
                Expression::BinaryOp(BinaryOp {
                    op_kind: BinaryOpKind::And,
                    left,
                    right,
                    position: _,
                }) if left.is_true() => *right,
                Expression::BinaryOp(BinaryOp {
                    op_kind: BinaryOpKind::And,
                    left,
                    right,
                    position: _,
                }) if right.is_true() => *left,
                Expression::BinaryOp(BinaryOp {
                    op_kind: BinaryOpKind::GeCmp,
                    left:
                        box Expression::Constant(Constant {
                            value: ConstantValue::Int(left_value),
                            ty: left_type,
                            ..
                        }),
                    right:
                        box Expression::Constant(Constant {
                            value: ConstantValue::Int(right_value),
                            ty: right_type,
                            ..
                        }),
                    position,
                }) => {
                    assert_eq!(left_type, right_type);
                    Expression::constant((left_value >= right_value).into(), Type::Bool, position)
                }
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
}
