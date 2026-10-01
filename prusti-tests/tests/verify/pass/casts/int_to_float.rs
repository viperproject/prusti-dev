fn main() {
    let x = 100;
    let y = x as f32;
    assert!(y == 100.0);

    let x = u8::MAX;
    let y = x as f64;
    assert!(y == 255.0);

    let x = -5;
    let y = x as f32;
    assert!(y == -5.0);

    let x = i8::MIN;
    let y = x as f32;
    assert!(y == -128.0);

    let x = 0i64;
    let y = x as f64;
    assert!(y == 0.0);

    // These casts are encoded, but their result can currently not be verified
    // using Z3 (see fail/casts/int_to_float.rs).
    let x = u128::MAX;
    let _y = x as f32;

    let _x = 9007199254740993i64 as f32;
}
