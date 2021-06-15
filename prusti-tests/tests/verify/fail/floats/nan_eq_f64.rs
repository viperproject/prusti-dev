fn main() {
    
    assert!(0.0_f64.is_nan()); //~ ERROR: the asserted expression might not hold

    let x:f64 = 0.99;
    assert!(x.is_nan()); //~ ERROR: the asserted expression might not hold

    let inf = f64::INFINITY;
    assert!(inf - inf == f64::NAN); //~ ERROR: the asserted expression might not hold

    assert!(f64::NAN == f64::NAN); //~ ERROR: the asserted expression might not hold

}
