fn main() {

    assert!((f64::NAN).is_nan());
    assert!(!0.0_f64.is_nan());

    let inf = f64::INFINITY;
    assert!((inf - inf).is_nan());

}