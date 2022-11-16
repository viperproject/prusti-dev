struct G {
    value: u32,
}

struct F {
    f: G,
    g: G,
}

fn consume_F(_f: F) {}

fn test7(y: F, z: F, b: bool) {
    let mut y = y;
    let mut z = z;
    let mut x;
    if b {
        x = &mut y;
    } else {
        x = &mut z;
    }
    let f = &mut x.f;
    consume_F(y);
    consume_F(z);
}

fn test6(y: F, z: F, b: bool) {
    let mut y = y;
    let mut z = z;
    let mut x;
    if b {
        x = &mut y;
        consume_F(z);
    } else {
        x = &mut z;
        consume_F(y);
    }
    let f = &mut x.f;
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

fn use_both(_f: &mut G, _g: &mut G) {}
