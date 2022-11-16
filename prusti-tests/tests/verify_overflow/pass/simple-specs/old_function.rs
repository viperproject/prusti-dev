use prusti_contracts::*;

struct T {
    x: u32,
}

#[pure]
fn get_x(t: &T) -> u32 {
    t.x
}

#[ensures(old(get_x(t)) == get_x(t))]
fn test(t: &mut T) {}

fn main() {}
