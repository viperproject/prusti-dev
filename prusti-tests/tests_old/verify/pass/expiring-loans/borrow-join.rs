use prusti_contracts::*;

struct G {
    value: u32,
}

fn test2(x: &mut G, b: bool) -> &mut u32 {
    let y;
    if b {
        y = x;
    } else {
        y = x;
    }
    let z = y;
    &mut z.value
}

fn main() {
}
