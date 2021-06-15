fn main() {

    // assert!(f32::NAN.is_nan()); // Somehow might not hold. Does for f64.

    assert!(!0.0_f32.is_nan());

    let inf = f32::INFINITY;
    assert!((inf - inf).is_nan());

}