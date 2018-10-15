#[feature(nll)]
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
    let z2 = &mut *z;
    let z3 = &mut *z;
}

fn main() {
}
