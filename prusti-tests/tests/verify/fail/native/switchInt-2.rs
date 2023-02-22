// compile-flags: -Pviper_backend=Lithium

fn test(x: i32) {
    match x {
        0..=100 => {
            assert!(x >= 0);
            assert!(x <= 100);
            assert!(x == 7); //~ ERROR might not hold
        }
        50 => {
            unreachable!();
        }
        _ => {
            assert!(x != 0);
            assert!(x < 0); //~ ERROR might not hold
        }
    }
}

fn main() {}
