use crate::*;

#[extern_spec]
trait Default {
    #[refine_spec(where Self: Copy + PureDefault, [pure])]
    fn default() -> Self;
}

/// Specifies that `Default::default`, if implemented, is a pure method, allowing its usage in specs.
///
/// Does not apply to types that do not implement `Copy`, since pure methods can only involve `Copy` types.
pub auto trait PureDefault {}

// analogous to https://github.com/rust-lang/rust/blob/872631d0f0fadffe3220ab1bd9c8f1f2342341e2/library/core/src/default.rs#L190-L202
macro_rules! default_spec {
    ($t:ty, $v:expr) => {
        #[extern_spec]
        impl Default for $t {
            #[pure]
            #[ensures(snapshot_equality(result, $v))]
            fn default() -> Self;
        }
    };
}

default_spec! { (), () }
default_spec! { bool, false }
default_spec! { char, '\x00' }

default_spec! { usize, 0 }
default_spec! { u8, 0 }
default_spec! { u16, 0 }
default_spec! { u32, 0 }
default_spec! { u64, 0 }
default_spec! { u128, 0 }

default_spec! { isize, 0 }
default_spec! { i8, 0 }
default_spec! { i16, 0 }
default_spec! { i32, 0 }
default_spec! { i64, 0 }
default_spec! { i128, 0 }

default_spec! { f32, 0.0f32 }
default_spec! { f64, 0.0f64 }

// specify behavior for tuples (have to rely on PureDefault)

// recursive like https://github.com/rust-lang/rust/blob/a5fa99eed20a46a88c0c85eed6552a94b6656634/library/core/src/tuple.rs#L10
macro_rules! specify_tuple_default {
    (impl $( $T:ident )*) => {
        #[extern_spec]
        impl<$($T,)*> Default for ($($T,)*) where
            $($T: Default,)*
        {
            #[refine_spec(where
                $($T: Copy + PureDefault,)*
            [
                pure,
                ensures(snapshot_equality(&result, &($($T::default(),)*))),
            ])]
            fn default() -> Self;
        }
    };
    (impls $T:ident $( $U:ident )+) => {
        specify_tuple_default!(impl $T $($U)+);
        specify_tuple_default!(impls $($U)+);
    };
    (impls $T:ident) => {
        specify_tuple_default!(impl $T);
    };
}

specify_tuple_default!(impls E D C B A Z Y X W V U T);

// more specific types

#[extern_spec]
impl<T> Default for Option<T> {
    #[refine_spec(where Self: Copy, [pure])]
    #[ensures(result.is_none())]
    fn default() -> Self;
}
