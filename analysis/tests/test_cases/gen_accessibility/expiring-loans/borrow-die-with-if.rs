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

fn use_both(_f: &mut G, _g: &mut G) {}
