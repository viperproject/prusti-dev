extern crate prusti_contracts;

struct G {
    value: u32,
}

struct F {
    f: G,
    g: G,
}

fn test1(x: &mut F) {
    let y = x;
    let z = y;
    let _z = &*z;
    let _z = &*_z;
    let _z = &*_z;
    let _z = &*_z;
    let _z = &*_z;
    let _z = &*_z;
    let _z = &*_z;
}

fn test2(x: &mut F, b: bool) {
    let y = &*x;
    let z = y;
    let z2;
    if b {
        z2 = z;
    } else {
        z2 = x;
    }
    let _z = z2;
    let _z = _z;
    let _z = &*_z;
    let _z = &*_z;
    let _z = &*_z;
    let _z = &*_z;
}

fn main() {
}
