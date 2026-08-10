use crate::*;

#[extern_spec]
impl f16 {
    #[trusted]
    #[pure]
    #[ensures(result == f16_is_nan(self))]
    fn is_nan(self) -> bool;

    #[trusted]
    #[pure]
    #[ensures(result == f16_is_infinite(self))]
    fn is_infinite(self) -> bool;

    #[trusted]
    #[pure]
    #[ensures(result == f16_abs(self))]
    fn abs(self) -> Self;
}

#[extern_spec]
impl f32 {
    #[trusted]
    #[pure]
    #[ensures(result == f32_is_nan(self))]
    fn is_nan(self) -> bool;

    #[trusted]
    #[pure]
    #[ensures(result == f32_is_infinite(self))]
    fn is_infinite(self) -> bool;

    #[trusted]
    #[pure]
    #[ensures(result == f32_abs(self))]
    fn abs(self) -> Self;
}

#[extern_spec]
impl f64 {
    #[trusted]
    #[pure]
    #[ensures(result == f64_is_nan(self))]
    fn is_nan(self) -> bool;

    #[trusted]
    #[pure]
    #[ensures(result == f64_is_infinite(self))]
    fn is_infinite(self) -> bool;

    #[trusted]
    #[pure]
    #[ensures(result == f64_abs(self))]
    fn abs(self) -> Self;
}

#[extern_spec]
impl f128 {
    #[trusted]
    #[pure]
    #[ensures(result == f128_is_nan(self))]
    fn is_nan(self) -> bool;

    #[trusted]
    #[pure]
    #[ensures(result == f128_is_infinite(self))]
    fn is_infinite(self) -> bool;

    #[trusted]
    #[pure]
    #[ensures(result == f128_abs(self))]
    fn abs(self) -> Self;
}
