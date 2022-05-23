use super::super::ast::{
    expression::{visitors::ExpressionFolder, *},
    ty::{visitors::TypeFolder, *},
    type_decl::DiscriminantValue,
};
use rustc_hash::FxHashMap;

impl Type {
    /// Return a type that represents a variant of the given enum.
    #[must_use]
    pub fn variant(self, variant: VariantIndex) -> Self {
        match self {
            Type::Enum(Enum {
                name,
                arguments,
                variant: None,
            }) => Type::Enum(Enum {
                name,
                arguments,
                variant: Some(variant),
            }),
            Type::Union(Union {
                name,
                arguments,
                variant: None,
            }) => Type::Union(Union {
                name,
                arguments,
                variant: Some(variant),
            }),
            Type::Enum(_) => {
                unreachable!("setting variant on enum type that already has variant set");
            }
            Type::Union(_) => {
                unreachable!("setting variant on union type that already has variant set");
            }
            _ => {
                unreachable!("setting variant on non-enum type");
            }
        }
    }
    /// Returns type with the type variant dropped if it had one. Otherwise,
    /// returns None.
    pub fn forget_variant(&self) -> Option<Self> {
        match self {
            Type::Enum(Enum {
                name,
                arguments,
                variant: Some(_),
            }) => Some(Type::Enum(Enum {
                name: name.clone(),
                arguments: arguments.clone(),
                variant: None,
            })),
            Type::Union(Union {
                name,
                arguments,
                variant: Some(_),
            }) => Some(Type::Union(Union {
                name: name.clone(),
                arguments: arguments.clone(),
                variant: None,
            })),
            _ => None,
        }
    }
    pub fn is_heap_primitive(&self) -> bool {
        self.is_bool() || self.is_int() || self.is_float()
    }
    pub fn has_variants(&self) -> bool {
        match self {
            Type::Enum(enum_ty) => enum_ty.variant.is_none(),
            Type::Union(union_ty) => union_ty.variant.is_none(),
            _ => false,
        }
    }
    pub fn erase_lifetime(&mut self) {
        if let Type::Reference(reference) = self {
            reference.lifetime = LifetimeConst::erased();
        }
    }
    pub fn erase_lifetimes(self) -> Self {
        struct DefaultLifetimeEraser {}
        impl TypeFolder for DefaultLifetimeEraser {
            fn fold_lifetime_const(&mut self, _lifetime: LifetimeConst) -> LifetimeConst {
                LifetimeConst::erased()
            }
        }
        DefaultLifetimeEraser {}.fold_type(self)
    }
    pub fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        if let Type::Reference(reference) = self {
            vec![reference.lifetime.clone()]
        } else {
            Vec::new()
        }
    }
}

impl AsRef<str> for VariantIndex {
    fn as_ref(&self) -> &str {
        &self.index
    }
}

impl super::super::ast::type_decl::Enum {
    pub fn get_variant(&self, ty: &Type) -> Option<&super::super::ast::type_decl::Struct> {
        if self.variants.len() == 1 {
            Some(&self.variants[0])
        } else {
            let variant_index = if let Type::Enum(enum_ty) = ty {
                &enum_ty.variant
            } else {
                return None;
            };
            self.variants.iter().find(|variant| {
                variant_index
                    .as_ref()
                    .map(|index| index.as_ref() == variant.name)
                    .unwrap_or(false)
            })
        }
    }
    pub fn get_discriminant(&self, variant_index: &VariantIndex) -> Option<DiscriminantValue> {
        self.iter_discriminant_variants()
            .find(|(_, variant)| variant_index.as_ref() == variant.name)
            .map(|(discriminant, _)| discriminant)
    }
    pub fn iter_discriminant_variants(
        &self,
    ) -> impl Iterator<Item = (DiscriminantValue, &super::super::ast::type_decl::Struct)> {
        self.discriminant_values.iter().cloned().zip(&self.variants)
    }
}

impl super::super::ast::type_decl::Union {
    pub fn get_discriminant(&self, variant_index: &VariantIndex) -> Option<DiscriminantValue> {
        self.iter_discriminant_variants()
            .find(|(_, variant)| variant_index.as_ref() == variant.name)
            .map(|(discriminant, _)| discriminant)
    }
    pub fn iter_discriminant_variants(
        &self,
    ) -> impl Iterator<Item = (DiscriminantValue, &super::super::ast::type_decl::Struct)> {
        self.discriminant_values.iter().cloned().zip(&self.variants)
    }
}

impl LifetimeConst {
    pub fn erased() -> Self {
        LifetimeConst {
            name: String::from("pure_erased"),
        }
    }
}

pub trait Generic {
    #[must_use]
    fn substitute_types(self, substs: &FxHashMap<TypeVar, Type>) -> Self;
}

impl Generic for Expression {
    fn substitute_types(self, substs: &FxHashMap<TypeVar, Type>) -> Self {
        struct TypeSubstitutor<'a> {
            substs: &'a FxHashMap<TypeVar, Type>,
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
    fn substitute_types(self, substs: &FxHashMap<TypeVar, Type>) -> Self {
        struct TypeSubstitutor<'a> {
            substs: &'a FxHashMap<TypeVar, Type>,
        }
        impl<'a> TypeFolder for TypeSubstitutor<'a> {
            fn fold_type_var_enum(&mut self, var: TypeVar) -> Type {
                if let Some(new_type) = self.substs.get(&var).cloned() {
                    new_type
                } else {
                    Type::TypeVar(var)
                }
            }
        }
        let mut substitutor = TypeSubstitutor { substs };
        substitutor.fold_type(self)
    }
}

// impl Generic for Vec<Type> {
//     fn substitute_types(self, substs: &FxHashMap<TypeVar, Type>) -> Self {
//         self.into_iter()
//                     .map(|arg| arg.substitute_types(substs))
//                     .collect()
//     }
// }

// impl Generic for Type {
//     fn substitute_types(self, substs: &FxHashMap<TypeVar, Type>) -> Self {
//         match self {
//             Type::Bool | Type::Int(_)  | Type::FnPointer | Type::Never | Type::Str => self,
//             Type::TypeVar(ref var) => substs.get(var).cloned().unwrap_or(self),
//             Type::Struct(Struct { name, arguments }) => Type::Struct(Struct {
//                 name,
//                 arguments: arguments.substitute_types(substs),
//             }),
//             Type::Enum(Enum {
//                 name,
//                 arguments,
//                 variant,
//             }) => Type::Enum(Enum {
//                 name,
//                 arguments: arguments.substitute_types(substs),
//                 variant,
//             }),
//             Type::Array(Array {
//                 length,
//                 element_type,
//             }) => Type::Array(Array {
//                 length,
//                 element_type: Box::new(element_type.substitute_types(substs)),
//             }),
//             Type::Slice(Slice { element_type }) => Type::Slice(Slice {
//                 element_type: Box::new(element_type.substitute_types(substs)),
//             }),
//             Type::Reference(Reference { target_type }) => Type::Reference(Reference {
//                 target_type: Box::new(target_type.substitute_types(substs)),
//             }),
//             Type::Pointer(Pointer { target_type }) => Type::Pointer(Pointer {
//                 target_type: Box::new(target_type.substitute_types(substs)),
//             }),
//         }
//     }
// }

pub trait Typed {
    fn get_type(&self) -> &Type;
    fn set_type(&mut self, new_type: Type);
}

impl Typed for Expression {
    fn get_type(&self) -> &Type {
        match self {
            Expression::Local(expression) => expression.get_type(),
            Expression::Constructor(expression) => expression.get_type(),
            Expression::Variant(expression) => expression.get_type(),
            Expression::Field(expression) => expression.get_type(),
            Expression::Deref(expression) => expression.get_type(),
            Expression::AddrOf(expression) => expression.get_type(),
            Expression::LabelledOld(expression) => expression.get_type(),
            Expression::Constant(expression) => expression.get_type(),
            Expression::UnaryOp(expression) => expression.get_type(),
            Expression::BinaryOp(expression) => expression.get_type(),
            Expression::ContainerOp(expression) => expression.get_type(),
            Expression::Seq(expression) => expression.get_type(),
            Expression::Conditional(expression) => expression.get_type(),
            Expression::Quantifier(expression) => expression.get_type(),
            Expression::LetExpr(expression) => expression.get_type(),
            Expression::FuncApp(expression) => expression.get_type(),
            Expression::BuiltinFuncApp(expression) => expression.get_type(),
            Expression::Downcast(expression) => expression.get_type(),
        }
    }
    fn set_type(&mut self, new_type: Type) {
        match self {
            Expression::Local(expression) => expression.set_type(new_type),
            Expression::Constructor(expression) => expression.set_type(new_type),
            Expression::Variant(expression) => expression.set_type(new_type),
            Expression::Field(expression) => expression.set_type(new_type),
            Expression::Deref(expression) => expression.set_type(new_type),
            Expression::AddrOf(expression) => expression.set_type(new_type),
            Expression::LabelledOld(expression) => expression.set_type(new_type),
            Expression::Constant(expression) => expression.set_type(new_type),
            Expression::UnaryOp(expression) => expression.set_type(new_type),
            Expression::BinaryOp(expression) => expression.set_type(new_type),
            Expression::ContainerOp(expression) => expression.set_type(new_type),
            Expression::Seq(expression) => expression.set_type(new_type),
            Expression::Conditional(expression) => expression.set_type(new_type),
            Expression::Quantifier(expression) => expression.set_type(new_type),
            Expression::LetExpr(expression) => expression.set_type(new_type),
            Expression::FuncApp(expression) => expression.set_type(new_type),
            Expression::BuiltinFuncApp(expression) => expression.set_type(new_type),
            Expression::Downcast(expression) => expression.set_type(new_type),
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

impl Typed for Constructor {
    fn get_type(&self) -> &Type {
        &self.ty
    }
    fn set_type(&mut self, new_type: Type) {
        self.ty = new_type;
    }
}
impl Typed for Variant {
    fn get_type(&self) -> &Type {
        &self.ty
    }
    fn set_type(&mut self, new_type: Type) {
        self.ty = new_type;
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

impl Typed for Deref {
    fn get_type(&self) -> &Type {
        &self.ty
    }
    fn set_type(&mut self, new_type: Type) {
        self.ty = new_type;
    }
}

impl Typed for AddrOf {
    fn get_type(&self) -> &Type {
        &self.ty
    }
    fn set_type(&mut self, new_type: Type) {
        self.ty = new_type;
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
            | BinaryOpKind::Mod
            | BinaryOpKind::LifetimeIntersection => {
                let ty1 = self.left.get_type();
                let ty2 = self.right.get_type();
                assert_eq!(ty1, ty2, "expr: {:?}", self);
                ty1
            }
        }
    }
    fn set_type(&mut self, new_type: Type) {
        self.left.set_type(new_type.clone());
        self.right.set_type(new_type);
    }
}

impl Typed for ContainerOp {
    fn get_type(&self) -> &Type {
        unimplemented!()
    }
    fn set_type(&mut self, _new_type: Type) {
        unimplemented!();
    }
}

impl Typed for Seq {
    fn get_type(&self) -> &Type {
        unimplemented!()
    }
    fn set_type(&mut self, _new_type: Type) {
        unimplemented!();
    }
}

impl Typed for Conditional {
    fn get_type(&self) -> &Type {
        let ty1 = self.then_expr.get_type();
        let ty2 = self.else_expr.get_type();
        assert_eq!(ty1, ty2, "expr: {:?}", self);
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
        unreachable!();
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

impl Typed for BuiltinFuncApp {
    fn get_type(&self) -> &Type {
        &self.return_type
    }
    fn set_type(&mut self, new_type: Type) {
        self.return_type = new_type;
    }
}

impl Typed for Downcast {
    fn get_type(&self) -> &Type {
        self.base.get_type()
    }
    fn set_type(&mut self, new_type: Type) {
        self.base.set_type(new_type);
    }
}
