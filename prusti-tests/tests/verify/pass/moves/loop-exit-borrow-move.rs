use prusti_contracts::*;

pub struct S(pub u32);

fn consume(_s: S) {}

// Each loop exit moves one of `a` and `b` and lends out the other. Assigning
// both after the loop must replace the value that is still held: adding a
// second predicate for the same place would make the path infeasible, which
// the refutation detects.
fn exits_move_or_lend(c: bool, d: bool) {
    let mut a = S(1);
    let mut b = S(2);
    let mut i = 0;
    let r;
    loop {
        if c {
            r = &mut a;
            consume(b);
            break;
        }
        if d {
            r = &mut b;
            consume(a);
            break;
        }
        body_invariant!(i < 100);
        if i >= 99 {
            return;
        }
        i += 1;
    }
    r.0 = 7;
    a = S(3);
    b = S(4);
    prusti_assert!(a.0 == 3 && b.0 == 4);
    prusti_refute!(false);
}
