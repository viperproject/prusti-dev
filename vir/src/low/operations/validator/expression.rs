use crate::{
    common::validator::{ValidationError, Validator},
    low::{ast::expression::*, operations::ty::Typed},
};

impl Validator for Expression {
    fn validate(&self) -> Result<(), ValidationError> {
        match self {
            Expression::Local(expression) => expression.validate(),
            Expression::Field(expression) => expression.validate(),
            Expression::LabelledOld(expression) => expression.validate(),
            Expression::Constant(expression) => expression.validate(),
            Expression::MagicWand(expression) => expression.validate(),
            Expression::PredicateAccessPredicate(expression) => expression.validate(),
            Expression::FieldAccessPredicate(expression) => expression.validate(),
            Expression::Unfolding(expression) => expression.validate(),
            Expression::UnaryOp(expression) => expression.validate(),
            Expression::BinaryOp(expression) => expression.validate(),
            Expression::PermBinaryOp(expression) => expression.validate(),
            Expression::ContainerOp(expression) => expression.validate(),
            Expression::Conditional(expression) => expression.validate(),
            Expression::Quantifier(expression) => expression.validate(),
            Expression::LetExpr(expression) => expression.validate(),
            Expression::FuncApp(expression) => expression.validate(),
            Expression::DomainFuncApp(expression) => expression.validate(),
            Expression::InhaleExhale(expression) => expression.validate(),
            Expression::SmtOperation(expression) => expression.validate(),
        }
    }
}

impl Validator for Local {
    fn validate(&self) -> Result<(), ValidationError> {
        Ok(())
    }
}

impl Validator for Field {
    fn validate(&self) -> Result<(), ValidationError> {
        self.base.validate()?;
        Ok(())
    }
}

impl Validator for LabelledOld {
    fn validate(&self) -> Result<(), ValidationError> {
        self.base.validate()?;
        Ok(())
    }
}

impl Validator for Constant {
    fn validate(&self) -> Result<(), ValidationError> {
        Ok(())
    }
}

impl Validator for MagicWand {
    fn validate(&self) -> Result<(), ValidationError> {
        self.left.validate()?;
        self.right.validate()?;
        Ok(())
    }
}

impl Validator for PredicateAccessPredicate {
    fn validate(&self) -> Result<(), ValidationError> {
        for argument in &self.arguments {
            argument.validate()?;
        }
        self.permission.validate()?;
        Ok(())
    }
}

impl Validator for FieldAccessPredicate {
    fn validate(&self) -> Result<(), ValidationError> {
        self.base.validate()?;
        self.permission.validate()?;
        Ok(())
    }
}

impl Validator for Unfolding {
    fn validate(&self) -> Result<(), ValidationError> {
        self.predicate.validate()?;
        self.base.validate()?;
        Ok(())
    }
}

impl Validator for UnaryOp {
    fn validate(&self) -> Result<(), ValidationError> {
        self.argument.validate()?;
        Ok(())
    }
}

impl Validator for BinaryOp {
    fn validate(&self) -> Result<(), ValidationError> {
        self.left.validate()?;
        self.right.validate()?;
        match self.op_kind {
            BinaryOpKind::EqCmp => {
                if self.left.get_type() != self.right.get_type() {
                    return Err(ValidationError::new(format!("Type mismatch: {self}")));
                }
            }
            BinaryOpKind::NeCmp => {}
            BinaryOpKind::GtCmp => {}
            BinaryOpKind::GeCmp => {}
            BinaryOpKind::LtCmp => {}
            BinaryOpKind::LeCmp => {}
            BinaryOpKind::Add => {}
            BinaryOpKind::Sub => {}
            BinaryOpKind::Mul => {
                if !matches!(self.left.get_type(), crate::low::ast::ty::Type::Int) {
                    return Err(ValidationError::new(format!(
                        "Multiplication requires integer: {self}"
                    )));
                }
                if !matches!(self.right.get_type(), crate::low::ast::ty::Type::Int) {
                    return Err(ValidationError::new(format!(
                        "Multiplication requires integer: {self}"
                    )));
                }
            }
            BinaryOpKind::Div => {}
            BinaryOpKind::Mod => {}
            BinaryOpKind::And => {}
            BinaryOpKind::Or => {}
            BinaryOpKind::Implies => {}
        }
        Ok(())
    }
}

impl Validator for PermBinaryOp {
    fn validate(&self) -> Result<(), ValidationError> {
        self.left.validate()?;
        self.right.validate()?;
        Ok(())
    }
}

impl Validator for ContainerOp {
    fn validate(&self) -> Result<(), ValidationError> {
        for operand in &self.operands {
            operand.validate()?;
        }
        Ok(())
    }
}

impl Validator for Conditional {
    fn validate(&self) -> Result<(), ValidationError> {
        self.guard.validate()?;
        self.then_expr.validate()?;
        self.else_expr.validate()?;
        Ok(())
    }
}

impl Validator for Trigger {
    fn validate(&self) -> Result<(), ValidationError> {
        for term in &self.terms {
            term.validate()?;
        }
        Ok(())
    }
}

impl Validator for Quantifier {
    fn validate(&self) -> Result<(), ValidationError> {
        for trigger in &self.triggers {
            trigger.validate()?;
        }
        self.body.validate()?;
        Ok(())
    }
}

impl Validator for LetExpr {
    fn validate(&self) -> Result<(), ValidationError> {
        self.def.validate()?;
        self.body.validate()?;
        Ok(())
    }
}

impl Validator for FuncApp {
    fn validate(&self) -> Result<(), ValidationError> {
        for argument in &self.arguments {
            argument.validate()?;
        }
        Ok(())
    }
}

impl Validator for DomainFuncApp {
    fn validate(&self) -> Result<(), ValidationError> {
        for argument in &self.arguments {
            argument.validate()?;
        }
        Ok(())
    }
}

impl Validator for InhaleExhale {
    fn validate(&self) -> Result<(), ValidationError> {
        self.inhale_expression.validate()?;
        self.exhale_expression.validate()?;
        Ok(())
    }
}

impl Validator for SmtOperation {
    fn validate(&self) -> Result<(), ValidationError> {
        for argument in &self.arguments {
            argument.validate()?;
        }
        Ok(())
    }
}
