use crate::*;

use core::default::Default;

// TODO: this should ideally be `#[refine_spec(where Self: PureDefault, [pure])]`
// (cf. `PartialEq::eq`), since not every `Default::default` is pure.
#[extern_spec]
trait Default {
    #[pure]
    fn default() -> Self;
}

macro_rules! int_default_spec {
    ($($t:ty),*) => {$(
        #[extern_spec]
        impl Default for $t {
            #[pure]
            #[ensures(result == 0)]
            fn default() -> $t;
        }
    )*}
}

int_default_spec!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);
