use crate::*;

pub auto trait PureFrom {}

#[extern_spec]
trait From<T> {
    #[refine_spec(where Self: Copy + PureFrom, T: Copy, [pure])]
    fn from(other: T) -> Self;
}

#[extern_spec]
impl<T, U> Into<U> for T
where
    U: From<T>,
{
    // When From is pure, we can use it to specify the behavior of Into
    #[refine_spec(where U: Copy + PureFrom, T: Copy, [
        pure,
        ensures(result === U::from(self))
    ])]
    // FUTURE(where_equality): we can specify the behavior of Into for identity conversions even if impure, but for that we need equality constraints
    // #[refine_spec(where T = U, [ensures(result === self)])]
    fn into(self) -> U;
}

// identity conversion
#[extern_spec]
impl<T> From<T> for T {
    #[ensures(result === other)]
    #[refine_spec(where T: Copy, [pure])]
    fn from(other: T) -> Self;
}

// numeric conversions

// specifies From<T> for lossless numeric conversions using as casts
macro_rules! specify_numeric_from {
    ($from:ty => $($to:ty)*) => ($(
        #[extern_spec]
        impl From<$from> for $to {
            #[pure]
            #[ensures(result == num as Self)]
            fn from(num: $from) -> Self;
        }
    )*)
}

specify_numeric_from!(bool => u8 i8 u16 i16 u32 i32 u64 i64 usize isize);

specify_numeric_from!(u8 => u16 i16 u32 i32 u64 i64 usize);
specify_numeric_from!(u16 => u32 i32 u64 i64);
specify_numeric_from!(u32 => u64 i64);
specify_numeric_from!(i8 => i16 i32 i64 isize);
specify_numeric_from!(i16 => i32 i64);
specify_numeric_from!(i32 => i64);
// size is not guaranteed to be at least 32 or at most 64 bits, so not valid for many conversions one might expect

// int-to-float conversions are exact when the int type has at most as many bits as the float's mantissa
specify_numeric_from!(u8 => f32 f64);
specify_numeric_from!(u16 => f32 f64);
specify_numeric_from!(u32 => f64);
specify_numeric_from!(i8 => f32 f64);
specify_numeric_from!(i16 => f32 f64);
specify_numeric_from!(i32 => f64);

specify_numeric_from!(f32 => f64);

#[cfg(version("1.26"))]
specify_numeric_from!(i16 => isize);
#[cfg(version("1.26"))]
specify_numeric_from!(u16 => usize);
#[cfg(version("1.26"))]
specify_numeric_from!(u8 => isize);
