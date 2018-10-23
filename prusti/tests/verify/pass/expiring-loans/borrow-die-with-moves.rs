extern crate prusti_contracts;

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

/*fn test3(y: &mut F) {
    let x = &mut *y;
    let f = &mut x.f;
    let g = &mut x.g;
    use_both(f, g);
}

fn test4(y: &mut F, z: &mut F) {
    let mut x = &mut *y;
    let f = &mut x.f;
    let g = &mut x.g;
    x = &mut *z;
    use_both(f, g);
    let f2 = &mut x.f;
}
*/

fn main() {}
