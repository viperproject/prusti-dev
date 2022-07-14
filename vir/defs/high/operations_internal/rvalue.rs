use super::{
    super::ast::{
        expression::Expression,
        position::Position,
        rvalue::{visitors::RvalueWalker, *},
        ty::*,
        variable::*,
    },
    ty::Typed,
};

impl Repeat {
    pub fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        self.argument.get_lifetimes()
    }
}

impl Ref {
    pub fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        let mut lifetimes = vec![self.operand_lifetime.clone()];
        lifetimes.extend(self.place_lifetimes.clone());
        lifetimes
    }
}

impl Reborrow {
    pub fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        let mut lifetimes = vec![self.operand_lifetime.clone()];
        lifetimes.extend(self.place_lifetimes.clone());
        lifetimes
    }
}

impl AddressOf {
    pub fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        self.place.get_lifetimes()
    }
}

impl Len {
    pub fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        self.place.get_lifetimes()
    }
}

impl BinaryOp {
    pub fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        let mut lifetimes = self.left.get_lifetimes();
        lifetimes.extend(self.right.get_lifetimes());
        lifetimes
    }
}

impl CheckedBinaryOp {
    pub fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        let mut lifetimes = self.left.get_lifetimes();
        lifetimes.extend(self.right.get_lifetimes());
        lifetimes
    }
}

impl UnaryOp {
    pub fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        self.argument.get_lifetimes()
    }
}

impl Discriminant {
    pub fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        self.place.get_lifetimes()
    }
}

impl Aggregate {
    pub fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        let mut lifetimes: Vec<LifetimeConst> = vec![];
        for operand in &self.operands {
            lifetimes.extend(operand.get_lifetimes());
        }
        let lifetimes_ty = self.ty.get_lifetimes();
        lifetimes.extend(lifetimes_ty);
        lifetimes
    }
}

impl Operand {
    pub fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        self.expression.get_lifetimes()
    }
}

impl Rvalue {
    pub fn check_no_default_position(&self) {
        struct Checker;
        impl RvalueWalker for Checker {
            fn walk_expression(&mut self, expression: &Expression) {
                expression.check_no_default_position();
            }
        }
        Checker.walk_rvalue(self)
    }

    pub fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        match self {
            Rvalue::Repeat(r) => r.get_lifetimes(),
            Rvalue::Ref(r) => r.get_lifetimes(),
            Rvalue::Reborrow(r) => r.get_lifetimes(),
            Rvalue::AddressOf(r) => r.get_lifetimes(),
            Rvalue::Len(r) => r.get_lifetimes(),
            Rvalue::BinaryOp(r) => r.get_lifetimes(),
            Rvalue::CheckedBinaryOp(r) => r.get_lifetimes(),
            Rvalue::UnaryOp(r) => r.get_lifetimes(),
            Rvalue::Discriminant(r) => r.get_lifetimes(),
            Rvalue::Aggregate(r) => r.get_lifetimes(),
        }
    }

    pub fn get_lifetimes_as_var(&self) -> Vec<VariableDecl> {
        let lifetimes_const = self.get_lifetimes();
        lifetimes_const
            .iter()
            .map(|lifetime| VariableDecl {
                name: lifetime.name.clone(),
                ty: Type::Lifetime,
            })
            .collect()
    }
}
