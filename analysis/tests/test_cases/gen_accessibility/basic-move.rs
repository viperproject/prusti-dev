pub struct S2 {
    f: u32,
}

pub fn test4() -> S2 {
    let x = S2 {
        f: 8,
    };
    let y = x;
    assert!(y.f == 9);
    y
}
