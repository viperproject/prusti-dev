// compile-flags: -Pviper_backend=Lithium

fn main() {
    assert!(true);
    assert!(false); //~ ERROR might not hold
}
