use super::{
    super::{
        super::ast::{
            expression::{
                visitors::{
                    default_fold_expression, default_fold_quantifier, default_walk_expression,
                    ExpressionFolder, ExpressionWalker,
                },
                Expression,
            },
            position::Position,
            rvalue::*,
            ty::{self, GenericType},
        },
        ty::Typed,
    },
    WithConstArguments,
};

impl WithConstArguments for Expression {
    fn get_const_arguments(&self) -> Vec<Expression> {
        pub struct ConstArgumentFinder {
            arguments: Vec<Expression>,
        }
        impl ExpressionWalker for ConstArgumentFinder {
            fn walk_variable_decl(&mut self, variable: &VariableDecl) {
                self.arguments.extend(variable.ty.get_const_arguments());
            }
        }
        let mut finder = ConstArgumentFinder {
            arguments: Vec::new(),
        };
        finder.walk_expression(self);
        finder.arguments
    }
}

impl WithConstArguments for Rvalue {
    fn get_const_arguments(&self) -> Vec<Expression> {
        match self {
            Self::Repeat(value) => value.get_const_arguments(),
            Self::AddressOf(value) => value.get_const_arguments(),
            Self::Len(value) => value.get_const_arguments(),
            Self::Cast(value) => value.get_const_arguments(),
            Self::BinaryOp(value) => value.get_const_arguments(),
            Self::CheckedBinaryOp(value) => value.get_const_arguments(),
            Self::UnaryOp(value) => value.get_const_arguments(),
            Self::Aggregate(value) => value.get_const_arguments(),
            Self::Discriminant(value) => value.get_const_arguments(),
            Self::Ref(value) => value.get_const_arguments(),
            Self::Reborrow(value) => value.get_const_arguments(),
        }
    }
}

impl WithConstArguments for Repeat {
    fn get_const_arguments(&self) -> Vec<Expression> {
        self.argument.get_const_arguments()
    }
}

impl WithConstArguments for Ref {
    fn get_const_arguments(&self) -> Vec<Expression> {
        self.place.get_const_arguments()
    }
}

impl WithConstArguments for Reborrow {
    fn get_const_arguments(&self) -> Vec<Expression> {
        self.deref_place.get_const_arguments()
    }
}

impl WithConstArguments for AddressOf {
    fn get_const_arguments(&self) -> Vec<Expression> {
        self.place.get_const_arguments()
    }
}

impl WithConstArguments for Len {
    fn get_const_arguments(&self) -> Vec<Expression> {
        self.place.get_const_arguments()
    }
}

impl WithConstArguments for Cast {
    fn get_const_arguments(&self) -> Vec<Expression> {
        let mut arguments = self.operand.get_const_arguments();
        arguments.extend(self.ty.get_const_arguments());
        arguments
    }
}

impl WithConstArguments for BinaryOp {
    fn get_const_arguments(&self) -> Vec<Expression> {
        let mut arguments = self.left.get_const_arguments();
        arguments.extend(self.right.get_const_arguments());
        arguments
    }
}

impl WithConstArguments for CheckedBinaryOp {
    fn get_const_arguments(&self) -> Vec<Expression> {
        let mut arguments = self.left.get_const_arguments();
        arguments.extend(self.right.get_const_arguments());
        arguments
    }
}

impl WithConstArguments for UnaryOp {
    fn get_const_arguments(&self) -> Vec<Expression> {
        self.argument.get_const_arguments()
    }
}

impl WithConstArguments for Discriminant {
    fn get_const_arguments(&self) -> Vec<Expression> {
        self.place.get_const_arguments()
    }
}

impl WithConstArguments for Aggregate {
    fn get_const_arguments(&self) -> Vec<Expression> {
        let mut arguments = vec![];
        for operand in &self.operands {
            arguments.extend(operand.get_const_arguments());
        }
        arguments.extend(self.ty.get_const_arguments());
        arguments
    }
}

impl WithConstArguments for Operand {
    fn get_const_arguments(&self) -> Vec<Expression> {
        self.expression.get_const_arguments()
    }
}
