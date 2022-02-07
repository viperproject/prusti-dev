pub(crate) macro derive_from_into_primitive($ConstantValue: ty, $ty: ty, $variant: ident) {
    impl From<$ty> for $ConstantValue {
        fn from(value: $ty) -> Self {
            Self::$variant(value.into())
        }
    }
}
pub(crate) macro derive_from_into_string($ConstantValue: ty, $ty: ty) {
    impl From<$ty> for $ConstantValue {
        fn from(value: $ty) -> Self {
            Self::BigInt(value.to_string())
        }
    }
}
pub(crate) macro derive_from($Constant: ty, $Expression: ty, $ty: ty, $vir_ty: expr) {
    impl From<$ty> for $Constant {
        fn from(value: $ty) -> Self {
            Self {
                value: value.into(),
                ty: $vir_ty,
                position: Default::default(),
            }
        }
    }
    impl From<$ty> for $Expression {
        fn from(value: $ty) -> Self {
            Self::Constant(value.into())
        }
    }
}
