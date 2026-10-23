//@ known-failure
fn i32_to_f32() {
    let x = 100;
    let y = x as f32;
    assert!(y == 100.0);
}

fn u8_to_f64() {
    let x = u8::MAX;
    let y = x as f64;
    assert!(y == 255.0);
}

fn negative_i32_to_f32() {
    let x = -5;
    let y = x as f32;
    assert!(y == -5.0);
}

fn i8_min_to_f32() {
    let x = i8::MIN;
    let y = x as f32;
    assert!(y == -128.0);
}

fn i64_to_f64() {
    let x = 0i64;
    let y = x as f64;
    assert!(y == 0.0);
}

// These casts are encoded, but their result can currently not be verified
// using Z3 (see fail/casts/int_to_float.rs).
fn unverified() {
    let x = u128::MAX;
    let _y = x as f32;

    let _x = 9007199254740993i64 as f32;
}
