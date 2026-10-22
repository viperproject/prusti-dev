use prusti_contracts::*;

// For large operands the rounding error exceeds the bound (e.g.
// `16777216.0 - 0.5` rounds to `16777216.0`), and the result may overflow.
#[requires(!x.is_nan() && !x.is_infinite())]
#[requires(!y.is_nan() && !y.is_infinite())]
#[ensures((Real::from(x) - Real::from(y)) - Real::from(result) <= Real::from(0.1))] //~ ERROR: postcondition might not hold
pub fn unbounded_sub(x: f32, y: f32) -> f32 {
    x - y
}

// Proving the first postcondition must not make the context inconsistent.
#[requires(!x.is_nan())]
#[requires(x >= 1.0 && x <= 100.0)]
#[ensures(Real::from(2.0) * Real::from(x) - Real::from(result) <= Real::from(0.1))]
#[ensures(false)] //~ ERROR: postcondition might not hold
pub fn real_post_then_false(x: f64) -> f64 {
    x + x
}

#[ensures(Real::from(0.1) == Real::from(0.2))] //~ ERROR: postcondition might not hold
pub fn distinct_literals() {}

#[requires(!x.is_nan() && x >= 1.0 && x <= 2.0)]
#[ensures(Real::from(result) == Real::from(2.0) * Real::from(x) + Real::from(1.0))] //~ ERROR: postcondition might not hold
pub fn wrong_value(x: f64) -> f64 {
    x + x
}
