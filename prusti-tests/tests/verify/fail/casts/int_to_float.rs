// The result of these casts can currently not be verified using Z3.
// Once Z3 supports these cases, replace pass/casts/int_to_float.rs with this file.

fn main() {
    let x = 100;
    let y = x as f32;
    assert!(y == 100.0); //~ERROR: the asserted expression might not hold

    let x = u128::MAX;
    let y = x as f32;
    assert!(y == f32::INFINITY); //~ERROR: the asserted expression might not hold

    let x = u8::MAX;
    let y = x as f64;
    assert!(y == 255.0); //~ERROR: the asserted expression might not hold

    let x = -5;
    let y = x as f32;
    assert!(y == -5.0); //~ERROR: the asserted expression might not hold

    let x = 9007199254740993i64;
    assert!(x as f32 == 9007199254740992.0); //~ERROR: the asserted expression might not hold
}