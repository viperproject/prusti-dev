fn main() {
    let a = 2.0;
    let b = 2.0;

    assert!(a / b != 1.0); //~ ERROR: the asserted expression might not hold
}