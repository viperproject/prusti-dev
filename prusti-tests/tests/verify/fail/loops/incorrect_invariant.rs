use prusti_contracts::*;

pub fn simple_loop() {
    let mut x = 0;
    while x < 100 {
        body_invariant!(x == 42); //~ ERROR loop invariant might not hold
        x += 1;
    }
}

fn main() {}
