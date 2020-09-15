use prusti_contracts::*;

fn main() {
    let mut i = 1000;

    // Note: the invariant is evaluated in the body, after the loop guard.
    // So, it is not `i >= 2` because inside the loop `i` is never `2`.
    // This design choice works well with complex loop guards, which can have side effects and can
    // even contain `return` statements.
    #[invariant(i > 2)]
    while i > 2 {
        i -= 1;
    }

    assert!(i == 2);
}
