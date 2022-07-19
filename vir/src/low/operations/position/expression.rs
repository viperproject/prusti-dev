use super::super::super::ast::expression::*;
use crate::common::position::Positioned;

impl Positioned for Expression {
    fn position(&self) -> Position {
        match self {
            Self::Local(expression) => expression.position(),
            Self::Field(expression) => expression.position(),
            Self::LabelledOld(expression) => expression.position(),
            Self::Constant(expression) => expression.position(),
            Self::MagicWand(expression) => expression.position(),
            Self::PredicateAccessPredicate(expression) => expression.position(),
            Self::FieldAccessPredicate(expression) => expression.position(),
            Self::Unfolding(expression) => expression.position(),
            Self::UnaryOp(expression) => expression.position(),
            Self::BinaryOp(expression) => expression.position(),
            Self::PermBinaryOp(expression) => expression.position(),
            Self::ContainerOp(expression) => expression.position(),
            Self::Seq(expression) => expression.position(),
            Self::Conditional(expression) => expression.position(),
            Self::Quantifier(expression) => expression.position(),
            Self::LetExpr(expression) => expression.position(),
            Self::FuncApp(expression) => expression.position(),
            Self::DomainFuncApp(expression) => expression.position(),
            Self::InhaleExhale(expression) => expression.position(),
            Self::MapOp(expression) => expression.position(),
        }
    }
}

impl Positioned for Local {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for Field {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for LabelledOld {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for Constant {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for MagicWand {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for PredicateAccessPredicate {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for FieldAccessPredicate {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for Unfolding {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for UnaryOp {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for BinaryOp {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for PermBinaryOp {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for ContainerOp {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for Seq {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for Conditional {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for Quantifier {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for LetExpr {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for FuncApp {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for DomainFuncApp {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for InhaleExhale {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for MapOp {
    fn position(&self) -> Position {
        self.position
    }
}
