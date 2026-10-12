use prusti_contracts::*;

// Moving a mutable reference twice, with its referent changed in between,
// must not make the state inconsistent.
pub fn test(x: &mut i32) {
    *x = 1;
    let y = x;
    *y = 7;
    let z = y;
    prusti_assert!(*z == 7);
    prusti_assert!(*z == 1); //~ ERROR: assertion might not hold
}

fn main() {}
