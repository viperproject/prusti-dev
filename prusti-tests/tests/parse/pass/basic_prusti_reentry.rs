use prusti_contracts::*;

// ignore-test: prusti-expr! not yet implemented
#[requires(x == 1 || prusti_expr!(y == 0 ==> z == 0))]
fn f(x: u32, y: u32, z: u32) -> u32 {
    return x + y + z;
}