extern crate prusti_contracts;

struct T {
    x: u32,
}

#[pure]
fn get_x(t: &mut T) -> u32 {
    t.x
}

#[ensures="old(get_x(t)) == 5"]
//#[ensures="old(get_x(t)) == get_x(t)"]    // Correct postcondition that also crashes.
// FP: The bug here is that we generate
// `old(get_x(unfolding bla in t))`
// instead of
// `old(unfolding bla in get_x(t))`
fn test(t: &mut T) {}

fn main() {}
