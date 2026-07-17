// This currently works with CVC5 but not with Z3..

fn main() {
    let x = 100;
    let y = x as f32;
    assert!(y == 100.0);

    let x = u128::MAX;
    let y = x as f32;
    assert!(y == f32::INFINITY);

    let x = u8::MAX;
    let y = x as f64;
    assert!(y == 255.0);

    let x = -5;
    let y = x as f32;
    assert!(y == -5.0);

    let x = 9007199254740993i64;
    assert!(x == 9007199254740993);
    assert!(x as f32 == 9007199254740992.0);
}