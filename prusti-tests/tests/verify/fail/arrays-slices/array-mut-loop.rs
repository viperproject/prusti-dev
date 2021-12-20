use prusti_contracts::*;

fn main() {}




fn looping() {
    let mut a = [0; 3];
    let mut i = 0;

    while i < 3 {
        body_invariant!(0 <= i && i < 3);

        a[i] = a[i];

        i += 1;
    }

    // NOTE: this seems true, but we can't prove it without a proper invariant
    // also this testcase is to error if we accidentally can verify the state from before the loop
    // afterwards without a proper invariant
    assert!(a[0] == 0);  //~ ERROR the asserted expression might not hold
}
