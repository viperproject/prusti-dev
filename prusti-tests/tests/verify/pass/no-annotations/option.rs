#![feature(box_patterns)]

fn main() {
    let x = 123;
    let y = Some(x);
    let z = if let Some(zz) = y { zz } else { panic!() };
    assert!(x == z);
}
