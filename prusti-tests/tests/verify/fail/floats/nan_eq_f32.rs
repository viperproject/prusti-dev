fn main() {
    
    // assert!(0.0_f32.is_nan()); 
    // assert!(!0.0_f32.is_nan());

    let b = 0.99_f32.is_nan();
    assert!(b); //~ ERROR: the asserted expression might not hold

    // let inf = f32::INFINITY;
    // assert!(inf - inf == f32::NAN); //~ ERROR: the asserted expression might not hold

    // assert!(f32::NAN == f32::NAN); //~ ERROR: the asserted expression might not hold

}