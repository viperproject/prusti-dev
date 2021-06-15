fn main() {
    
    assert!(0.0_f32.is_nan()); 
    assert!(!0.0_f32.is_nan());
    // let x:f32 = 0.99;
    // assert!(x.is_nan()); //~ ERROR: the asserted expression might not hold

    // let inf = f32::INFINITY;
    // assert!(inf - inf == f32::NAN); //~ ERROR: the asserted expression might not hold

    // assert!(f32::NAN == f32::NAN); //~ ERROR: the asserted expression might not hold

}