use super::{
    super::{
        super::ast::{
            expression::visitors::{
                default_fold_expression, default_fold_quantifier, default_walk_expression,
                ExpressionFolder, ExpressionWalker,
            },
            position::Position,
            rvalue::*,
            ty::{self, LifetimeConst},
        },
        ty::Typed,
    },
    WithLifetimes,
};

pub(super) fn get_lifetimes_with_arguments(
    lifetimes: &[ty::LifetimeConst],
    arguments: &Vec<ty::Type>,
) -> Vec<ty::LifetimeConst> {
    let mut all_lifetimes = lifetimes.to_owned();
    for ty in arguments {
        for lifetime in ty.get_lifetimes() {
            if !all_lifetimes.contains(&lifetime) {
                all_lifetimes.push(lifetime);
            }
        }
    }
    all_lifetimes
}

impl WithLifetimes for Expression {
    fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        pub struct LifetimeFinder {
            lifetimes: Vec<LifetimeConst>,
        }
        impl ExpressionWalker for LifetimeFinder {
            fn walk_variable_decl(&mut self, variable: &VariableDecl) {
                self.lifetimes.extend(variable.ty.get_lifetimes());
            }
        }
        let mut finder = LifetimeFinder { lifetimes: vec![] };
        finder.walk_expression(self);
        finder.lifetimes
    }
}

impl WithLifetimes for Rvalue {
    fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        match self {
            Self::Repeat(value) => value.get_lifetimes(),
            Self::AddressOf(value) => value.get_lifetimes(),
            Self::Len(value) => value.get_lifetimes(),
            Self::Cast(value) => value.get_lifetimes(),
            Self::BinaryOp(value) => value.get_lifetimes(),
            Self::CheckedBinaryOp(value) => value.get_lifetimes(),
            Self::UnaryOp(value) => value.get_lifetimes(),
            Self::Aggregate(value) => value.get_lifetimes(),
            Self::Discriminant(value) => value.get_lifetimes(),
            Self::Ref(value) => value.get_lifetimes(),
            Self::Reborrow(value) => value.get_lifetimes(),
        }
    }
}

impl WithLifetimes for Repeat {
    fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        self.argument.get_lifetimes()
    }
}

impl WithLifetimes for Ref {
    fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        let mut lifetimes = vec![self.new_borrow_lifetime.clone()];
        lifetimes.extend(self.place.get_type().get_lifetimes());
        lifetimes
    }
}

impl WithLifetimes for Reborrow {
    fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        let mut lifetimes = vec![self.new_borrow_lifetime.clone()];
        lifetimes.extend(self.deref_place.get_type().get_lifetimes());
        lifetimes
    }
}

impl WithLifetimes for AddressOf {
    fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        self.place.get_lifetimes()
    }
}

impl WithLifetimes for Len {
    fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        self.place.get_lifetimes()
    }
}

impl WithLifetimes for Cast {
    fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        let mut lifetimes = self.operand.get_lifetimes();
        lifetimes.extend(self.ty.get_lifetimes());
        lifetimes
    }
}

impl WithLifetimes for BinaryOp {
    fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        let mut lifetimes = self.left.get_lifetimes();
        lifetimes.extend(self.right.get_lifetimes());
        lifetimes
    }
}

impl WithLifetimes for CheckedBinaryOp {
    fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        let mut lifetimes = self.left.get_lifetimes();
        lifetimes.extend(self.right.get_lifetimes());
        lifetimes
    }
}

impl WithLifetimes for UnaryOp {
    fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        self.argument.get_lifetimes()
    }
}

impl WithLifetimes for Discriminant {
    fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        self.place.get_lifetimes()
    }
}

impl WithLifetimes for Aggregate {
    fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        let mut lifetimes: Vec<LifetimeConst> = vec![];
        for operand in &self.operands {
            lifetimes.extend(operand.get_lifetimes());
        }
        let lifetimes_ty = self.ty.get_lifetimes();
        lifetimes.extend(lifetimes_ty);
        lifetimes
    }
}

impl WithLifetimes for Operand {
    fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        self.expression.get_lifetimes()
    }
}
