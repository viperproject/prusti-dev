extern crate prusti_contracts;

struct G {
    value: u32,
}

struct F {
    f: G,
    g: G,
}

fn consume_F(_f: F) {}

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

fn use_one(_f: &mut u32) {}

fn use_both(_f: &mut G, _g: &mut G) {
}

fn main() {
}
