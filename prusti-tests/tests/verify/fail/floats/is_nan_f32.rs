fn main() {
    
    assert!(0.99_f32.is_nan()); //~ ERROR: the asserted expression might not hold

    let inf = f32::INFINITY;
    assert!(!(inf - inf).is_nan()); //~ ERROR: the asserted expression might not hold

}