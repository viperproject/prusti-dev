use prusti_contracts::*;

fn main() {}

fn looping() {
    let mut a = [0; 3];

    let mut i = 0;
    while i < 3 {
        body_invariant!(0 <= i && i < 3);
        a[i] = i;

        i += 1;
    }

    assert!(i == 3);
}
