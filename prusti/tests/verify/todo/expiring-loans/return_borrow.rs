
struct G {
    value: u32,
}

struct F {
    f: G,
    g: G,
}

fn test1(x: &mut F) -> &mut G {
    let y = x;
    let z = y;
    let z = &mut *z;
    let z = &mut *z;
    let z = &mut *z;
    let z = &mut *z;
    let z = &mut *z;
    let z = &mut *z;
    let z = &mut *z;
    &mut z.f
}

fn test2(x: &mut F, b: bool) -> &mut G {
    let y = &mut *x;
    let z = y;
    let z2;
    if b {
        z2 = z;
    } else {
        z2 = x;
    }
    let z = z2;
    let z = z;
    let z = &mut *z;
    let z = &mut *z;
    let z = &mut *z;
    let z = &mut *z;
    &mut z.g
}

fn main() {
}
