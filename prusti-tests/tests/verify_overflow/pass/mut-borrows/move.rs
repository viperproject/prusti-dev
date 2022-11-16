use prusti_contracts::*;

struct T {
    f: u32,
}

#[ensures(*x == 4)]
fn test1(x: &mut u32) {
    *x = 4;
}

#[ensures(x.f == 4)]
fn test2(x: &mut T) {
    let a = T {
        f: 4,
    };
    *x = a;
}

fn main() {}
