use super::super::ast::{
    expression::{self, *},
    ty::{self, *},
};

impl Type {
    pub fn is_place(&self) -> bool {
        if let Type::Domain(domain) = self {
            domain.name == crate::common::builtin_constants::PLACE_DOMAIN_NAME
        } else {
            false
        }
    }

    pub fn is_place_option(&self) -> bool {
        if let Type::Domain(domain) = self {
            domain.name == crate::common::builtin_constants::PLACE_OPTION_DOMAIN_NAME
        } else {
            false
        }
    }

    pub fn is_address(&self) -> bool {
        if let Type::Domain(domain) = self {
            domain.name == crate::common::builtin_constants::ADDRESS_DOMAIN_NAME
        } else {
            false
        }
    }

    pub fn is_lifetime(&self) -> bool {
        if let Type::Domain(domain) = self {
            domain.name == crate::common::builtin_constants::LIFETIME_DOMAIN_NAME
        } else {
            false
        }
    }

    pub fn is_bytes(&self) -> bool {
        if let Type::Domain(domain) = self {
            domain.name == crate::common::builtin_constants::BYTES_DOMAIN_NAME
        } else {
            false
        }
    }
}

pub trait Typed {
    fn get_type(&self) -> &Type;
    fn set_type(&mut self, new_type: Type);
}

impl Typed for Expression {
    fn get_type(&self) -> &Type {
        match self {
            Expression::Local(expression) => expression.get_type(),
            Expression::Field(expression) => expression.get_type(),
            Expression::LabelledOld(expression) => expression.get_type(),
            Expression::Constant(expression) => expression.get_type(),
            Expression::MagicWand(expression) => expression.get_type(),
            Expression::PredicateAccessPredicate(expression) => expression.get_type(),
            Expression::FieldAccessPredicate(expression) => expression.get_type(),
            Expression::Unfolding(expression) => expression.get_type(),
            Expression::UnaryOp(expression) => expression.get_type(),
            Expression::BinaryOp(expression) => expression.get_type(),
            Expression::PermBinaryOp(expression) => expression.get_type(),
            Expression::ContainerOp(expression) => expression.get_type(),
            Expression::Conditional(expression) => expression.get_type(),
            Expression::Quantifier(expression) => expression.get_type(),
            Expression::LetExpr(expression) => expression.get_type(),
            Expression::FuncApp(expression) => expression.get_type(),
            Expression::DomainFuncApp(expression) => expression.get_type(),
            Expression::InhaleExhale(expression) => expression.get_type(),
        }
    }
    fn set_type(&mut self, new_type: Type) {
        match self {
            Expression::Local(expression) => expression.set_type(new_type),
            Expression::Field(expression) => expression.set_type(new_type),
            Expression::LabelledOld(expression) => expression.set_type(new_type),
            Expression::Constant(expression) => expression.set_type(new_type),
            Expression::MagicWand(expression) => expression.set_type(new_type),
            Expression::PredicateAccessPredicate(expression) => expression.set_type(new_type),
            Expression::FieldAccessPredicate(expression) => expression.set_type(new_type),
            Expression::Unfolding(expression) => expression.set_type(new_type),
            Expression::UnaryOp(expression) => expression.set_type(new_type),
            Expression::BinaryOp(expression) => expression.set_type(new_type),
            Expression::PermBinaryOp(expression) => expression.set_type(new_type),
            Expression::ContainerOp(expression) => expression.set_type(new_type),
            Expression::Conditional(expression) => expression.set_type(new_type),
            Expression::Quantifier(expression) => expression.set_type(new_type),
            Expression::LetExpr(expression) => expression.set_type(new_type),
            Expression::FuncApp(expression) => expression.set_type(new_type),
            Expression::DomainFuncApp(expression) => expression.set_type(new_type),
            Expression::InhaleExhale(expression) => expression.set_type(new_type),
        }
    }
}

impl Typed for Local {
    fn get_type(&self) -> &Type {
        &self.variable.ty
    }
    fn set_type(&mut self, new_type: Type) {
        self.variable.ty = new_type;
    }
}

impl Typed for Field {
    fn get_type(&self) -> &Type {
        &self.field.ty
    }
    fn set_type(&mut self, new_type: Type) {
        self.field.ty = new_type;
    }
}

impl Typed for LabelledOld {
    fn get_type(&self) -> &Type {
        self.base.get_type()
    }
    fn set_type(&mut self, new_type: Type) {
        self.base.set_type(new_type);
    }
}

impl Typed for Constant {
    fn get_type(&self) -> &Type {
        &self.ty
    }
    fn set_type(&mut self, new_type: Type) {
        self.ty = new_type;
    }
}

impl Typed for MagicWand {
    fn get_type(&self) -> &Type {
        &Type::Bool
    }
    fn set_type(&mut self, _new_type: Type) {
        unreachable!("tried to set type for MagicWand");
    }
}

impl Typed for PredicateAccessPredicate {
    fn get_type(&self) -> &Type {
        &Type::Bool
    }
    fn set_type(&mut self, _new_type: Type) {
        unreachable!("tried to set type for MagicWand");
    }
}

impl Typed for FieldAccessPredicate {
    fn get_type(&self) -> &Type {
        &Type::Bool
    }
    fn set_type(&mut self, _new_type: Type) {
        unreachable!("tried to set type for MagicWand");
    }
}

impl Typed for Unfolding {
    fn get_type(&self) -> &Type {
        self.base.get_type()
    }
    fn set_type(&mut self, new_type: Type) {
        self.base.set_type(new_type)
    }
}

impl Typed for UnaryOp {
    fn get_type(&self) -> &Type {
        self.argument.get_type()
    }
    fn set_type(&mut self, new_type: Type) {
        self.argument.set_type(new_type);
    }
}

impl Typed for BinaryOp {
    fn get_type(&self) -> &Type {
        match self.op_kind {
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
            | BinaryOpKind::Mod => {
                let ty1 = self.left.get_type();
                let ty2 = self.right.get_type();
                assert_eq!(ty1, ty2, "expr: {self:?}");
                ty1
            }
        }
    }
    fn set_type(&mut self, new_type: Type) {
        assert!(
            !matches!(
                self.op_kind,
                BinaryOpKind::EqCmp
                    | BinaryOpKind::NeCmp
                    | BinaryOpKind::GtCmp
                    | BinaryOpKind::GeCmp
                    | BinaryOpKind::LtCmp
                    | BinaryOpKind::LeCmp
                    | BinaryOpKind::And
                    | BinaryOpKind::Or
                    | BinaryOpKind::Implies
            ),
            "cannot change the type of {:?}",
            self.op_kind
        );
        self.left.set_type(new_type.clone());
        self.right.set_type(new_type);
    }
}

impl Typed for PermBinaryOp {
    fn get_type(&self) -> &Type {
        &Type::Perm
    }
    fn set_type(&mut self, new_type: Type) {
        assert_eq!(new_type, Type::Perm);
    }
}

impl Typed for ContainerOp {
    fn get_type(&self) -> &Type {
        match self.kind {
            ContainerOpKind::SeqEmpty
            | ContainerOpKind::SeqConstructor
            | ContainerOpKind::SeqConcat
            | ContainerOpKind::MapEmpty
            | ContainerOpKind::MapUpdate
            | ContainerOpKind::SetEmpty
            | ContainerOpKind::SetConstructor
            | ContainerOpKind::SetUnion
            | ContainerOpKind::SetIntersection
            | ContainerOpKind::SetMinus
            | ContainerOpKind::MultiSetEmpty
            | ContainerOpKind::MultiSetConstructor
            | ContainerOpKind::MultiSetUnion
            | ContainerOpKind::MultiSetIntersection
            | ContainerOpKind::MultiSetMinus => &self.container_type,
            ContainerOpKind::SeqLen
            | ContainerOpKind::MapLen
            | ContainerOpKind::SetCardinality
            | ContainerOpKind::MultiSetCardinality => &Type::Int,
            ContainerOpKind::MapContains
            | ContainerOpKind::SetSubset
            | ContainerOpKind::SetContains
            | ContainerOpKind::MultiSetSubset
            | ContainerOpKind::MultiSetContains => &Type::Bool,
            ContainerOpKind::SeqIndex => match &self.container_type {
                Type::Seq(ty::Seq { element_type, .. }) => element_type,
                _ => unreachable!("Expected Seq type, got {:?}", self.container_type),
            },
            ContainerOpKind::MapLookup => match &self.container_type {
                Type::Map(ty::Map { val_type, .. }) => val_type,
                _ => unreachable!("Expected Seq type, got {:?}", self.container_type),
            },
        }
    }
    fn set_type(&mut self, new_type: Type) {
        assert_eq!(
            self.get_type(),
            &new_type,
            "Changing the type of ContainerOp."
        );
    }
}

impl Typed for Conditional {
    fn get_type(&self) -> &Type {
        let ty1 = self.then_expr.get_type();
        let ty2 = self.else_expr.get_type();
        assert_eq!(ty1, ty2, "expr: {self:?}");
        ty1
    }
    fn set_type(&mut self, new_type: Type) {
        self.then_expr.set_type(new_type.clone());
        self.else_expr.set_type(new_type);
    }
}

impl Typed for Quantifier {
    fn get_type(&self) -> &Type {
        &Type::Bool
    }
    fn set_type(&mut self, _new_type: Type) {
        unreachable!("tried to set type for Quantifier");
    }
}

impl Typed for LetExpr {
    fn get_type(&self) -> &Type {
        self.body.get_type()
    }
    fn set_type(&mut self, new_type: Type) {
        self.body.set_type(new_type)
    }
}

impl Typed for FuncApp {
    fn get_type(&self) -> &Type {
        &self.return_type
    }
    fn set_type(&mut self, new_type: Type) {
        self.return_type = new_type;
    }
}

impl Typed for DomainFuncApp {
    fn get_type(&self) -> &Type {
        &self.return_type
    }
    fn set_type(&mut self, new_type: Type) {
        self.return_type = new_type;
    }
}

impl Typed for InhaleExhale {
    fn get_type(&self) -> &Type {
        &Type::Bool
    }
    fn set_type(&mut self, _new_type: Type) {
        unreachable!("tried to set type for InhaleExhale");
    }
}
