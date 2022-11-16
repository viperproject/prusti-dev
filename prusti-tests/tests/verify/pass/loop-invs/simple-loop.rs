use prusti_contracts::*;

fn main() {
    let mut i = 10;
    while i > 0 {
        body_invariant!(i <= 10);
        i -= 1;
    }
}
