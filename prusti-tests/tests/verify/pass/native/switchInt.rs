// compile-flags: -Pviper_backend=Lithium

fn test(x: i32) {
    match x {
        0..=5 => {
            assert!(x >= 0);
            assert!(x <= 5);
        }
        1 => {
            assert!(x == 1);
        }
        _ => {
            assert!(x < 0 || x >= 0);
        }
    }
}

fn main() {}
