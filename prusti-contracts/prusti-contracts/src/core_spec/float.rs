use crate::*;

#[extern_spec]
impl f16 {
    #[pure]
    #[ensures(result == f16_is_nan(self))]
    fn is_nan(self) -> bool;

    #[pure]
    #[ensures(result == f16_is_infinite(self))]
    fn is_infinite(self) -> bool;

    #[pure]
    #[ensures(result == f16_abs(self))]
    fn abs(self) -> Self;
}

#[extern_spec]
impl f32 {
    #[pure]
    #[ensures(result == f32_is_nan(self))]
    fn is_nan(self) -> bool;

    #[pure]
    #[ensures(result == f32_is_infinite(self))]
    fn is_infinite(self) -> bool;

    #[pure]
    #[ensures(result == f32_abs(self))]
    fn abs(self) -> Self;
}

#[extern_spec]
impl f64 {
    #[pure]
    #[ensures(result == f64_is_nan(self))]
    fn is_nan(self) -> bool;

    #[pure]
    #[ensures(result == f64_is_infinite(self))]
    fn is_infinite(self) -> bool;

    #[pure]
    #[ensures(result == f64_abs(self))]
    fn abs(self) -> Self;
}

#[extern_spec]
impl f128 {
    #[pure]
    #[ensures(result == f128_is_nan(self))]
    fn is_nan(self) -> bool;

    #[pure]
    #[ensures(result == f128_is_infinite(self))]
    fn is_infinite(self) -> bool;

    #[pure]
    #[ensures(result == f128_abs(self))]
    fn abs(self) -> Self;
}
