fn main() {
    let a = 1.;
    let b = 0.;

    assert!(a / b != f64::NAN); //~ ERROR: the asserted expression might not hold
}