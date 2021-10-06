use super::super::ast::{
    expression::{visitors::ExpressionFolder, *},
    ty::*,
};
use std::collections::HashMap;

pub trait Generic {
    fn substitute_types(self, substs: &HashMap<TypeVar, Type>) -> Self;
}

impl Generic for Expression {
    fn substitute_types(self, substs: &HashMap<TypeVar, Type>) -> Self {
        struct TypeSubstitutor<'a> {
            substs: &'a HashMap<TypeVar, Type>,
        }
        impl<'a> ExpressionFolder for TypeSubstitutor<'a> {
            fn fold_type(&mut self, ty: Type) -> Type {
                ty.substitute_types(self.substs)
            }
        }
        let mut substitutor = TypeSubstitutor { substs };
        substitutor.fold_expression(self)
    }
}

impl Generic for Type {
    fn substitute_types(self, substs: &HashMap<TypeVar, Type>) -> Self {
        match self {
            Type::Int | Type::Bool | Type::FnPointer => self,
            Type::TypeVar(ref var) => substs.get(var).cloned().unwrap_or(self),
            Type::Struct(Struct { name, arguments }) => Type::Struct(Struct {
                name,
                arguments: arguments
                    .into_iter()
                    .map(|arg| arg.substitute_types(substs))
                    .collect(),
            }),
            Type::Enum(Enum {
                name,
                arguments,
                variant,
            }) => Type::Enum(Enum {
                name,
                arguments: arguments
                    .into_iter()
                    .map(|arg| arg.substitute_types(substs))
                    .collect(),
                variant,
            }),
            Type::Array(Array {
                length,
                element_type,
            }) => Type::Array(Array {
                length,
                element_type: Box::new(element_type.substitute_types(substs)),
            }),
            Type::Slice(Slice { element_type }) => Type::Slice(Slice {
                element_type: Box::new(element_type.substitute_types(substs)),
            }),
            Type::Reference(Reference { target_type }) => Type::Reference(Reference {
                target_type: Box::new(target_type.substitute_types(substs)),
            }),
            Type::Pointer(Pointer { target_type }) => Type::Pointer(Pointer {
                target_type: Box::new(target_type.substitute_types(substs)),
            }),
        }
    }
}

pub trait Typed {
    fn get_type(&self) -> &Type;
}

impl Typed for Expression {
    fn get_type(&self) -> &Type {
        match self {
            Expression::Local(expression) => expression.get_type(),
            Expression::Variant(expression) => expression.get_type(),
            Expression::Field(expression) => expression.get_type(),
            Expression::Deref(expression) => expression.get_type(),
            Expression::AddrOf(expression) => expression.get_type(),
            Expression::LabelledOld(expression) => expression.get_type(),
            Expression::Constant(expression) => expression.get_type(),
            Expression::UnaryOp(expression) => expression.get_type(),
            Expression::BinOp(expression) => expression.get_type(),
            Expression::ContainerOp(expression) => expression.get_type(),
            Expression::Seq(expression) => expression.get_type(),
            Expression::Conditional(expression) => expression.get_type(),
            Expression::Quantifier(expression) => expression.get_type(),
            Expression::LetExpr(expression) => expression.get_type(),
            Expression::FuncApp(expression) => expression.get_type(),
            Expression::Downcast(expression) => expression.get_type(),
        }
    }
}

impl Typed for Local {
    fn get_type(&self) -> &Type {
        &self.variable.ty
    }
}

impl Typed for Variant {
    fn get_type(&self) -> &Type {
        &self.ty
    }
}

impl Typed for Field {
    fn get_type(&self) -> &Type {
        &self.field.ty
    }
}

impl Typed for Deref {
    fn get_type(&self) -> &Type {
        &self.ty
    }
}

impl Typed for AddrOf {
    fn get_type(&self) -> &Type {
        &self.ty
    }
}

impl Typed for LabelledOld {
    fn get_type(&self) -> &Type {
        self.base.get_type()
    }
}

impl Typed for Constant {
    fn get_type(&self) -> &Type {
        match &self.value {
            ConstantValue::Bool(_) => &Type::Bool,
            ConstantValue::Int(_) | ConstantValue::BigInt(_) => &Type::Int,
            ConstantValue::FnPtr => &Type::FnPointer,
        }
    }
}

impl Typed for UnaryOp {
    fn get_type(&self) -> &Type {
        self.argument.get_type()
    }
}

impl Typed for BinOp {
    fn get_type(&self) -> &Type {
        match self.op_kind {
            BinOpKind::EqCmp
            | BinOpKind::NeCmp
            | BinOpKind::GtCmp
            | BinOpKind::GeCmp
            | BinOpKind::LtCmp
            | BinOpKind::LeCmp
            | BinOpKind::And
            | BinOpKind::Or
            | BinOpKind::Implies => &Type::Bool,
            BinOpKind::Add | BinOpKind::Sub | BinOpKind::Mul | BinOpKind::Div | BinOpKind::Mod => {
                let ty1 = self.left.get_type();
                let ty2 = self.right.get_type();
                assert_eq!(ty1, ty2, "expr: {:?}", self);
                ty1
            }
        }
    }
}

impl Typed for ContainerOp {
    fn get_type(&self) -> &Type {
        unimplemented!()
    }
}

impl Typed for Seq {
    fn get_type(&self) -> &Type {
        unimplemented!()
    }
}

impl Typed for Conditional {
    fn get_type(&self) -> &Type {
        let ty1 = self.then_expr.get_type();
        let ty2 = self.else_expr.get_type();
        assert_eq!(ty1, ty2, "expr: {:?}", self);
        ty1
    }
}

impl Typed for Quantifier {
    fn get_type(&self) -> &Type {
        &Type::Bool
    }
}

impl Typed for LetExpr {
    fn get_type(&self) -> &Type {
        &self.variable.ty
    }
}

impl Typed for FuncApp {
    fn get_type(&self) -> &Type {
        &self.return_type
    }
}

impl Typed for Downcast {
    fn get_type(&self) -> &Type {
        self.base.get_type()
    }
}
