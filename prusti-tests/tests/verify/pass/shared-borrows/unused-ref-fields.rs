use prusti_contracts::*;

struct T<'a> {
    f: u32,
    g: &'a u32,
    h: *const u32,
    i: Vec<u32>,
    j: String,
    k: &'a [T<'a>],
}

#[requires(x.f == 123)]
#[ensures(result == 123)]
fn test(x: &T) -> u32 {
    x.f
}

fn main() {}
