#[feature(nll)]
extern crate prusti_contracts;

struct G {
    value: u32,
}

struct F {
    f: G,
    g: G,
}

fn use_mut_ref(x: &mut F) {}

fn main() {}
