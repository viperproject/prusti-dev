use prusti_contracts::*;

#[ensures()]
fn no_args() {}

#[requires[true]]
fn square_brackets() {
    let mut i = 0u32;
    while i < 10 {
        i += 1
    }
}

fn main() {}
