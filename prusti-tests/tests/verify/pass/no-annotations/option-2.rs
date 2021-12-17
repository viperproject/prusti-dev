/// From crate `103_crossbeam-epoch`

struct Wrap<P>(P);

fn test(x: Option<Wrap<u32>>) -> Wrap<u32> {
    Wrap(123)
}

fn main() {}
