struct G {
    value: u32,
}

struct F {
    f: G,
    g: G,
}

fn consume_F(_f: F) {}

fn use_both(_f: &mut G, _g: &mut G) {}

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
