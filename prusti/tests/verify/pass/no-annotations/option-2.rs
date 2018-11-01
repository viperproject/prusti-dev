/// From crate `103_crossbeam-epoch`

extern crate prusti_contracts;

struct Wrap<P>(P);

fn test(x: Option<Wrap<u32>>) -> Wrap<u32> {
    Wrap(123)
}

fn main() {}
