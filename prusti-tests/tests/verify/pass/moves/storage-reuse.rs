use prusti_contracts::*;

// The guard temporary `t` is assigned before the loop head and again on the
// exiting iteration. Its first value must be dropped when its storage dies:
// if it were leaked, the second assignment would add another predicate for
// the same place, and merging the two (0 and 3) would make the path
// infeasible, which the refutation detects.
fn guard_temp() {
    let mut i = 0;
    while {
        let t = i;
        t < 3
    } {
        body_invariant!(0 <= i && i < 3);
        i += 1;
    }
    prusti_refute!(false);
}
