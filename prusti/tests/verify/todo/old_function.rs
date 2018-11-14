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
fn test(t: &mut T) {}

fn main() {}
