// compile-flags: -Pviper_backend=Lithium

fn test(x: i32) {
    match x {
        0 => {
            assert!(false); //~ ERROR might not hold
        }
        1 => {
            assert!(false); //~ ERROR might not hold
        }
        2 => {
            assert!(true);
        }
        _ => {
            assert!(false); //~ ERROR might not hold
        }
    }
}

fn main() {}
