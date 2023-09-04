use crate::*;

#[allow(unused_imports)]
use core::ops::*;

macro_rules! specify_ref_op {
    (impl $trait:tt fn $name:ident as $op:tt for $($t:ty)*) => ($(
        #[extern_spec]
        impl $trait<$t> for &$t {
            #[pure]
            #[ensures(result == *self $op other)]
            fn $name(self, other: $t) -> $t;
        }

        #[extern_spec]
        impl $trait<&$t> for $t {
            #[pure]
            #[ensures(result == self $op *other)]
            fn $name(self, other: &$t) -> $t;
        }

        #[extern_spec]
        impl $trait<&$t> for &$t {
            #[pure]
            #[ensures(result == *self $op *other)]
            fn $name(self, other: &$t) -> $t;
        }
    )*)
}

specify_ref_op! { impl Add fn add as + for usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 f32 f64 }
specify_ref_op! { impl Sub fn sub as - for usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 f32 f64 }
specify_ref_op! { impl Mul fn mul as * for usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 f32 f64 }
specify_ref_op! { impl Div fn div as / for usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 f32 f64 }
specify_ref_op! { impl Rem fn rem as % for usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 f32 f64 }

// FUTURE(bitvectors): bitwise operations on non-boolean types are experimental (`encode_bitvectors` to enable). could specify: usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128
specify_ref_op! { impl BitAnd fn bitand as & for bool }
specify_ref_op! { impl BitOr fn bitor as | for bool }
specify_ref_op! { impl BitXor fn bitxor as ^ for bool }

// FUTURE(bitvectors): left/right shifts. these will need special care since LHS and RHS may have different types

macro_rules! specify_ref_op_assign {
    (impl $trait:tt fn $name:ident as $op:tt for $($t:ty)*) => ($(
        #[extern_spec]
        impl $trait<&$t> for $t {
            #[ensures(*self == old(*self) $op *other)]
            fn $name(&mut self, other: &$t);
        }
    )*)
}

specify_ref_op_assign! { impl AddAssign fn add_assign as + for usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 f32 f64 }
specify_ref_op_assign! { impl SubAssign fn sub_assign as - for usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 f32 f64 }
specify_ref_op_assign! { impl MulAssign fn mul_assign as * for usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 f32 f64 }
specify_ref_op_assign! { impl DivAssign fn div_assign as / for usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 f32 f64 }
specify_ref_op_assign! { impl RemAssign fn rem_assign as % for usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 f32 f64 }

// FUTURE(bitvectors): bitwise operations on non-boolean types are experimental (`encode_bitvectors` to enable). could specify: usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128
specify_ref_op_assign! { impl BitAndAssign fn bitand_assign as & for bool }
specify_ref_op_assign! { impl BitOrAssign fn bitor_assign as | for bool }
specify_ref_op_assign! { impl BitXorAssign fn bitxor_assign as ^ for bool }

// FUTURE(bitvectors): left/right shifts. these will need special care since LHS and RHS may have different types
