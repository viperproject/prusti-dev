use super::ty::Typed;
use crate::{
    common::expression::SyntacticEvaluation,
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
                name: format!("_{}", i),
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
                name: format!("_{}", i),
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
            "{} → {}",
            target,
            replacement
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
                if local.variable.name == "self$" {
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
        }
        PlaceReplacer { replacements }.fold_expression(self)
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
        }
        LabelReplacer { old_label }.fold_expression(self)
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
    pub fn no_permission() -> Self {
        Self::constant_no_pos(0.into(), Type::Perm)
    }
    pub fn wildcard_permission() -> Self {
        Self::constant_no_pos((-1i64).into(), Type::Perm)
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
        let simplified = Simplifier.fold_expression(self);
        simplified
    }
}
