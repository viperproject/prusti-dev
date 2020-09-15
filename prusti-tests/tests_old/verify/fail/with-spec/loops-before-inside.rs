use prusti_contracts::*;

fn test_invariant_on_entry() -> i32 {
    let mut x = 0;
    while x < 10 {
        body_invariant!(false); //~ ERROR loop invariant might not hold in the first loop iteration
        x += 1;
    }
    x
}

fn test_invariant_after_loop_iteration() -> i32 {
    let mut x = 0;
    while x < 10 {
        body_invariant!(x == 0); //~ ERROR loop invariant might not hold after a loop iteration
        x += 1;
    }
    x
}

fn main() {}
