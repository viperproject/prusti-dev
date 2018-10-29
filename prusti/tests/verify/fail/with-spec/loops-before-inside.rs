
fn test_invariant_on_entry() -> i32 { //~ ERROR loop invariant might not hold on entry
    let mut x = 0;
    #[invariant="false"]
    while x < 10 {
        x += 1;
    }
    x
}

fn test_invariant_after_loop_iteration() -> i32 { //~ ERROR loop invariant might not hold after one loop iteration
    let mut x = 0;
    #[invariant="x == 0"]
    while x < 10 {
        x += 1;
    }
    x
}

fn main() {}
