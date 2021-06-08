fn main() {
    let a = 5.0;
    let b = -1.0;

    assert!(a - b != 6.0); //~ ERROR: the asserted expression might not hold
}