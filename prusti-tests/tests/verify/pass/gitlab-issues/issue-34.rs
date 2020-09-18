use prusti_contracts::*;

struct T {
    f: u32,
}

#[pure]
fn get_f(s: &T) -> u32 {
    s.f
}

fn main() {
    let a = T {
        f: 5,
    };
    let b = get_f(&a);
    assert!(b == 5);
}
