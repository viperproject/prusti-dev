// The result of these casts can currently not be verified using Z3: the cost
// of `int2bv` grows with the magnitude of the converted value.
// Once Z3 can prove these, move the assertions to pass/casts/int_to_float.rs.

fn max_u128() {
    let x = u128::MAX;
    let y = x as f32;
    assert!(y == f32::INFINITY); //~ERROR: precondition of `core::panicking::panic` (called by this macro expansion) might not hold
}

fn rounding() {
    let x = 9007199254740993i64;
    assert!(x as f32 == 9007199254740992.0); //~ERROR: precondition of `core::panicking::panic` (called by this macro expansion) might not hold
}

fn main() {}
