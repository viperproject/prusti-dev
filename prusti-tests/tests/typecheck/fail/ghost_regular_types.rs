use prusti_contracts::GhostInt;


fn test_ghost_regular_sum() -> GhostInt {
    let a = GhostInt;
    let b = 10;
    a + b //~ ERROR mismatched types
}

// ghost code should not interfere with regular code
fn test_ghost_arguments(arg1: GhostInt, arg2: &i32) {
    *arg2 = arg1 //~ ERROR mismatched types
}

fn main() {}
