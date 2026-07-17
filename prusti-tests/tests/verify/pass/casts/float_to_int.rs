fn main() {
    let x = 100.0;
    let y = x as i32;
    assert!(y == 100);

    let x2 = 36.9;
    let y2 = x2 as u32;
    assert!(y2 == 36);

    let x3 = -36.9;
    let y3 = x3 as u32;
    assert!(y3 == 0);

    let x4 = -36.9;
    let y4 = x4 as i32;
    assert!(y4 == -36);

    let x5 = 1000.5;
    let y5 = x5 as u8;
    assert!(y5 == 255);

    let x6 = -1000.5;
    let y6 = x6 as i8;
    assert!(y6 == -128);

    let x7 = -36.3;
    let y7 = x7 as i32;
    assert!(y7 == -36);

    let x8 = f64::INFINITY;
    let y8 = x8 as i32;
    assert!(y8 == i32::MAX);

    let x9 = f64::NEG_INFINITY;
    let y9 = x9 as i32;
    assert!(y9 == i32::MIN);

    let x10 = f64::NAN;
    let y10 = x10 as i32;
    assert!(y10 == 0);
}