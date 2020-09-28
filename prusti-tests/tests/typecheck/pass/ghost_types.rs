use prusti_contracts::*;
use crate::ghost::GhostInt;

fn test_ghost_int_sum() -> GhostInt{
    let a = GhostInt;
    let b = GhostInt;
    a + b
}

// ghost method
fn test_ghost_arguments(arg1: GhostInt, arg2: GhostInt) -> GhostInt {
    arg1 + arg2
}
// TODO: Extend the tests to account for non-interference properties of ghost code
fn main() {}
