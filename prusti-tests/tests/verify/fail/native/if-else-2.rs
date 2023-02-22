// compile-flags: -Pviper_backend=Lithium

fn main() {
    let x: i32 = 37;
    if x == 37 {
        assert!(x == 3); //~ ERROR might not hold
    } else {
        assert!(x == 3);
    }
}
