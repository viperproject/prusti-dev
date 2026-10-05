// The result of these casts can currently not be verified using Z3: the cost
// of `int2bv` grows with the magnitude of the converted value.
// Once Z3 can prove these, move the assertions to pass/casts/int_to_float.rs.

use prusti_contracts::*;

fn max_u128() {
    let x = u128::MAX;
    let y = x as f32;
    prusti_assert!(y == f32::INFINITY); //~ERROR: assertion might not hold
}

fn rounding() {
    let x = 9007199254740993i64;
    prusti_assert!(x as f32 == 9007199254740992.0); //~ERROR: assertion might not hold
}

fn large_magnitude() {
    prusti_assert!(i128::MIN as f32 == -170141183460469231731687303715884105728.0);
    //~ERROR: assertion might not hold
}
