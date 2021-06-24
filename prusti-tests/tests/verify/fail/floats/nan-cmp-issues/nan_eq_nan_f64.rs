// ignore-test: link to the issue
fn main() {
    assert!(f64::NAN == f64::NAN); //~ ERROR: the asserted expression might not hold
    // assert!(f64::NAN != f64::NAN);
}