use super::super::ast::{
    expression::{visitors::ExpressionFolder, *},
    ty::{
        visitors::{default_walk_reference, default_walk_type, TypeFolder, TypeWalker},
        *,
    },
    type_decl::DiscriminantValue,
    variable::VariableDecl,
};
use rustc_hash::FxHashMap;
use std::collections::BTreeMap;

impl Type {
    /// Return a type that represents a variant of the given enum.
    #[must_use]
    pub fn variant(self, variant: VariantIndex) -> Self {
        match self {
            Type::Enum(Enum {
                name,
                safety,
                arguments,
                variant: None,
                lifetimes,
            }) => Type::Enum(Enum {
                name,
                safety,
                arguments,
                variant: Some(variant),
                lifetimes,
            }),
            Type::Enum(_) => {
                unreachable!("setting variant on enum type that already has variant set");
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
                safety,
                arguments,
                variant: Some(_),
                lifetimes,
            }) => Some(Type::Enum(Enum {
                name: name.clone(),
                safety: *safety,
                arguments: arguments.clone(),
                variant: None,
                lifetimes: lifetimes.clone(),
            })),
            _ => None,
        }
    }
    /// Returns type with the type variant dropped if it had one. Otherwise,
    /// returns None.
    pub fn split_off_variant(&self) -> Option<(Self, &VariantIndex)> {
        match self {
            Type::Enum(Enum {
                name,
                safety,
                arguments,
                variant: Some(variant),
                lifetimes,
            }) => Some((
                Type::Enum(Enum {
                    name: name.clone(),
                    safety: *safety,
                    arguments: arguments.clone(),
                    variant: None,
                    lifetimes: lifetimes.clone(),
                }),
                variant,
            )),
            _ => None,
        }
    }
    pub fn is_heap_primitive(&self) -> bool {
        self.is_bool() || self.is_int() || self.is_float()
    }
    pub fn has_variants(&self) -> bool {
        match self {
            Type::Enum(enum_ty) => enum_ty.variant.is_none(),
            _ => false,
        }
    }
    #[must_use]
    pub fn erase_lifetimes(&self) -> Self {
        struct DefaultLifetimeEraser {}
        impl TypeFolder for DefaultLifetimeEraser {
            fn fold_lifetime_const(&mut self, _lifetime: LifetimeConst) -> LifetimeConst {
                LifetimeConst::erased()
            }
        }
        DefaultLifetimeEraser {}.fold_type(self.clone())
    }
    pub fn check_no_erased_lifetime(&self) {
        struct LifetimeChecker {}
        impl TypeWalker for LifetimeChecker {
            fn walk_lifetime_const(&mut self, lifetime: &LifetimeConst) {
                assert_ne!(lifetime.name, LifetimeConst::erased().name);
            }
        }
        LifetimeChecker {}.walk_type(self);
    }
    #[must_use]
    pub fn replace_lifetimes(
        self,
        lifetime_replacement_map: &BTreeMap<LifetimeConst, LifetimeConst>,
    ) -> Self {
        struct Replacer<'a> {
            lifetime_replacement_map: &'a BTreeMap<LifetimeConst, LifetimeConst>,
        }
        impl<'a> TypeFolder for Replacer<'a> {
            fn fold_lifetime_const(&mut self, lifetime: LifetimeConst) -> LifetimeConst {
                self.lifetime_replacement_map
                    .get(&lifetime)
                    .unwrap_or_else(|| panic!("Not found lifetime: {}", lifetime))
                    .clone()
            }
        }
        Replacer {
            lifetime_replacement_map,
        }
        .fold_type(self)
    }
    #[must_use]
    pub fn replace_lifetime(
        self,
        old_lifetime: &LifetimeConst,
        new_lifetime: &LifetimeConst,
    ) -> Self {
        struct Replacer<'a> {
            old_lifetime: &'a LifetimeConst,
            new_lifetime: &'a LifetimeConst,
        }
        impl<'a> TypeFolder for Replacer<'a> {
            fn fold_lifetime_const(&mut self, lifetime: LifetimeConst) -> LifetimeConst {
                if &lifetime == self.old_lifetime {
                    self.new_lifetime.clone()
                } else {
                    lifetime
                }
            }
        }
        Replacer {
            old_lifetime,
            new_lifetime,
        }
        .fold_type(self)
    }
    #[must_use]
    pub fn erase_const_generics(self) -> Self {
        struct Eraser {}
        impl TypeFolder for Eraser {
            fn fold_const_generic_argument(
                &mut self,
                mut argument: ConstGenericArgument,
            ) -> ConstGenericArgument {
                argument.value = None;
                argument
            }
        }
        Eraser {}.fold_type(self)
    }
    #[must_use]
    pub fn normalize_type(&self) -> Self {
        self.erase_lifetimes().erase_const_generics()
    }
    pub fn contains_type_variables(&self) -> bool {
        match self {
            Self::Sequence(Sequence { element_type, .. })
            | Self::Array(Array { element_type, .. })
            | Self::Slice(Slice { element_type, .. }) => element_type.is_type_var(),
            Self::Reference(Reference { target_type, .. })
            | Self::Pointer(Pointer { target_type, .. }) => target_type.is_type_var(),
            Self::Map(ty) => ty.key_type.is_type_var() || ty.val_type.is_type_var(),
            Self::TypeVar(_) => true,
            Self::Trusted(Trusted { arguments, .. })
            | Self::Struct(Struct { arguments, .. })
            | Self::Enum(Enum { arguments, .. })
            | Self::Projection(Projection { arguments, .. }) => {
                arguments.iter().any(|arg| arg.is_type_var())
            }
            Self::Closure(_) => {
                unimplemented!();
            }
            Self::FunctionDef(_) => {
                unimplemented!();
            }
            Self::Unsupported(_) => true,
            _ => false,
        }
    }
    pub fn is_pointer_to_slice(&self) -> bool {
        if let Type::Pointer(Pointer { target_type, .. }) = self {
            target_type.is_slice()
        } else {
            false
        }
    }
    pub fn is_reference_to_slice(&self) -> bool {
        if let Type::Reference(Reference { target_type, .. }) = self {
            target_type.is_slice()
        } else {
            false
        }
    }
    pub fn is_unique_reference(&self) -> bool {
        if let Type::Reference(Reference { uniqueness, .. }) = self {
            uniqueness.is_unique()
        } else {
            false
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

impl LifetimeConst {
    pub fn erased() -> Self {
        LifetimeConst {
            name: String::from(crate::common::builtin_constants::ERASED_LIFETIME_NAME),
        }
    }
}

impl From<LifetimeConst> for VariableDecl {
    fn from(lifetime: LifetimeConst) -> Self {
        Self::new(lifetime.name, Type::Lifetime)
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
            Expression::Final(expression) => expression.get_type(),
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
            Expression::AccPredicate(expression) => expression.get_type(),
            Expression::Unfolding(expression) => expression.get_type(),
            Expression::EvalIn(expression) => expression.get_type(),
        }
    }
    fn set_type(&mut self, new_type: Type) {
        match self {
            Expression::Local(expression) => expression.set_type(new_type),
            Expression::Constructor(expression) => expression.set_type(new_type),
            Expression::Variant(expression) => expression.set_type(new_type),
            Expression::Field(expression) => expression.set_type(new_type),
            Expression::Deref(expression) => expression.set_type(new_type),
            Expression::Final(expression) => expression.set_type(new_type),
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
            Expression::AccPredicate(expression) => expression.set_type(new_type),
            Expression::Unfolding(expression) => expression.set_type(new_type),
            Expression::EvalIn(expression) => expression.set_type(new_type),
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

impl Typed for Final {
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

impl Typed for AccPredicate {
    fn get_type(&self) -> &Type {
        &Type::Bool
    }
    fn set_type(&mut self, _new_type: Type) {
        unreachable!();
    }
}

impl Typed for Unfolding {
    fn get_type(&self) -> &Type {
        self.body.get_type()
    }
    fn set_type(&mut self, new_type: Type) {
        self.body.set_type(new_type)
    }
}

impl Typed for EvalIn {
    fn get_type(&self) -> &Type {
        self.body.get_type()
    }
    fn set_type(&mut self, new_type: Type) {
        self.body.set_type(new_type)
    }
}
