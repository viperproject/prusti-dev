use prusti_contracts::*;

fn main() {}

fn looping() {
    let mut a = [0; 3];

    let mut i = 0;
    let mut cont = true;
    while cont {
        body_invariant!(0 <= i && i < 3);
        a[i] = i;

        i += 1;
        cont = i < 3;
    }

    assert!(i == 3);
}
