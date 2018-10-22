extern crate prusti_contracts;

fn test_invariant_on_entry() -> i32 {
    let mut x = 0;
    #[invariant="false"]
    while x < 10 { //~ ERROR loop invariant might not hold on entry
        x += 1;
    }
    x
}

fn test_invariant_after_loop_iteration() -> i32 {
    let mut x = 0;
    #[invariant="x == 0"]
    while x < 10 { //~ ERROR loop invariant might not hold after one loop iteration
        x += 1;
    }
    x
}

fn main() {}
