extern crate prusti_contracts;

struct G {
    value: u32,
}

struct F {
    f: G,
    g: G,
}

fn test5(y: &mut F, z: &mut F, z2: &mut G, b: bool) {
    let mut x = &mut *y;
    let f = &mut x.f;
    let mut g;
    if b {
        g = &mut x.g;
    } else {
        g = z2;
        g = &mut *g;
    }
    x = &mut *z;
    use_both(f, g);
    let f2 = &mut x.f;
}

fn test4(y: &mut F, z: &mut F) {
    let mut x = &mut *y;
    let f = &mut x.f;
    let g = &mut x.g;
    x = &mut *z;
    use_both(f, g);
    let f2 = &mut x.f;
}


fn test1(x: &mut F) {
    let y = x;
    let z = y;
    let _z = &mut *z;
    let _z = &mut *_z;
    let _z = &mut *_z;
    let _z = &mut *_z;
    let _z = &mut *_z;
    let _z = &mut *_z;
    let _z = &mut *_z;
}

fn test2(x: &mut F, b: bool) {
    let y = &mut *x;
    let z = y;
    let z2;
    if b {
        z2 = z;
    } else {
        z2 = x;
    }
    let _z = z2;
    let _z = _z;
    let _z = &mut *_z;
    let _z = &mut *_z;
    let _z = &mut *_z;
    let _z = &mut *_z;
}

fn test3(y: &mut F) {
    let x = &mut *y;
    let f = &mut x.f;
    let g = &mut x.g;
    use_both(f, g);
}

fn use_both(_f: &mut G, _g: &mut G) {
}

fn main() {
}
