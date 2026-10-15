use prusti_contracts::*;

#[ensures(Real::from(x) == Real::from(result))]
pub fn foo(x: f32) -> f32 {
    x
}

// Disabled: `Real::from` of a non-constant float is encoded as `fp.to_real`,
// which Z3 cannot reason about (it gives up or exhausts its resource limit).
// Z3 4.16 may even answer `unsat` here (Z3Prover/z3#9022), which made these
// pass vacuously.

// #[requires(!x.is_nan())]
// #[requires(x >= 1.0 && x <= 100.0)]
// #[ensures(Real::from(2.0) * Real::from(x) - Real::from(result) <= Real::from(0.1))]
// #[ensures(-Real::from(0.1) <= Real::from(2.0) * Real::from(x) - Real::from(result))]
// pub fn foo2(x: f64) -> f64 {
//     x + x
// }

// #[requires(!x.is_nan() && x >= -100.0 && x <= 100.0)]
// #[requires(!y.is_nan() && y >= -100.0 && y <= 100.0)]
// #[ensures((Real::from(x) - Real::from(y)) - Real::from(result) <= Real::from(0.1))]
// #[ensures(-Real::from(0.1) <= (Real::from(x) - Real::from(y)) - Real::from(result))]
// pub fn foo3(x: f32, y: f32) -> f32 {
//     x - y
// }

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