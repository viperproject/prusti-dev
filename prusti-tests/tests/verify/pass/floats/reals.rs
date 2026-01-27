use prusti_contracts::*;

#[ensures(Real::from(x) == Real::from(result))]
pub fn foo(x: f32) -> f32 {
    x
}

#[requires(!x.is_nan())]
#[requires(x >= 1.0 && x <= 100.0)]
#[ensures(Real::from(2.0) * Real::from(x) - Real::from(result) <= Real::from(0.1))]
#[ensures(-Real::from(0.1) <= Real::from(2.0) * Real::from(x) - Real::from(result))]
pub fn foo2(x: f64) -> f64 {
    x + x
}

#[requires(!x.is_nan())]
#[requires(!f32_is_infinite(x))]
#[requires(!y.is_nan())]
#[requires(y != f32::INFINITY && y != -f32::INFINITY)]
#[ensures((Real::from(x) - Real::from(y)) - Real::from(result) <= Real::from(0.1))]
#[ensures(-Real::from(0.1) <= (Real::from(x) - Real::from(y)) - Real::from(result))]
pub fn foo3(x: f32, y: f32) -> f32 {
    x - y
}

#[ensures(Real::from(1.0) <= Real::from(2.0))]
pub fn foo4(){}

#[ensures(Real::from(0.0) == Real::from(-0.0))]
pub fn foo5(){}

#[ensures(Real::from(2.5) > Real::from(2.0))]
pub fn foo6(){}

#[ensures(Real::from(8.5) / Real::from(2.0) == Real::from(4.25))]
pub fn foo7(){}

#[ensures(-Real::from(8.5) == Real::from(-8.5))]
pub fn foo8(){}