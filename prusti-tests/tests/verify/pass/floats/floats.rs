use prusti_contracts::*;

#[requires(f == 2.0)]
#[ensures(result == f)]
fn foo(f: f32) -> f32 {
    f
}

#[requires(f == 2.0)]
#[ensures(result == 2.5)]
fn foo2(f: f32) -> f32 {
    f + 0.5
}

#[requires(f == 4.5)]
#[ensures(result == 1.5)]
fn foo3(f: f32) -> f32 {
    f % 3.0
}

#[requires(f == 4.25)]
#[ensures(result == 1.25)]
fn foo4(f: f32) -> f32 {
    f % 3.0
}

#[requires(!f32_is_nan(f))]
#[ensures(result == f)]
fn foo5(f: f32) -> f32 {
    f
}

#[requires(!f.is_nan())]
#[ensures(result == f)]
fn foo6(f: f64) -> f64 {
    f
}

#[requires(!x.is_nan())]
#[requires(!y.is_nan())]
#[ensures(result == if x > y { 4 } else { 2 })]
fn foo7(x: f32, y: f32) -> u8 {
    if y < x {
        4
    } else {
        2
    }
}

#[requires(!x.is_nan())]
#[requires(!y.is_nan())]
#[requires(x != y)]
#[ensures(!result)]
fn foo8(x: f32, y: f32) -> bool {
    x == 2.5 && y == 2.5
}

#[requires(x == 3.3)]
#[ensures(result == -3.3)]
fn foo9(x: f32) -> f32 {
    -x
}

#[requires(!x.is_nan())]
#[requires(!x.is_infinite())]
#[ensures(!result.is_infinite())]
fn foo10(x: f32) -> f32 {
    x
}

#[requires(x == 4.5)]
#[ensures((result - (2.0 * x)).abs() <= 0.01)]
fn times_two(x: f32) -> f32 {
    x + x
}
