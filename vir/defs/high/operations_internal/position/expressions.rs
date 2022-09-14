use super::super::super::ast::expression::*;
use crate::common::position::Positioned;

impl Positioned for Expression {
    fn position(&self) -> Position {
        match self {
            Self::Local(expression) => expression.position(),
            Self::Constructor(expression) => expression.position(),
            Self::Variant(expression) => expression.position(),
            Self::Field(expression) => expression.position(),
            Self::Deref(expression) => expression.position(),
            Self::Final(expression) => expression.position(),
            Self::AddrOf(expression) => expression.position(),
            Self::LabelledOld(expression) => expression.position(),
            Self::Constant(expression) => expression.position(),
            Self::UnaryOp(expression) => expression.position(),
            Self::BinaryOp(expression) => expression.position(),
            Self::ContainerOp(expression) => expression.position(),
            Self::Seq(expression) => expression.position(),
            Self::Conditional(expression) => expression.position(),
            Self::Quantifier(expression) => expression.position(),
            Self::LetExpr(expression) => expression.position(),
            Self::FuncApp(expression) => expression.position(),
            Self::Downcast(expression) => expression.position(),
            Self::BuiltinFuncApp(expression) => expression.position(),
            Self::AccPredicate(expression) => expression.position(),
            Self::Unfolding(expression) => expression.position(),
            Self::EvalIn(expression) => expression.position(),
        }
    }
}

impl Positioned for Local {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for Constructor {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for Variant {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for Field {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for Deref {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for Final {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for AddrOf {
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

impl Positioned for BuiltinFuncApp {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for Downcast {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for AccPredicate {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for Unfolding {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for EvalIn {
    fn position(&self) -> Position {
        self.position
    }
}
