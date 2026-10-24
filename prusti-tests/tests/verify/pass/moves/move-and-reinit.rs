use prusti_contracts::*;

pub struct S {
    pub v: i32,
}

fn consume(_s: S) {}

fn consume_b(_s: S) -> bool {
    true
}

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

// `x` is moved out on one branch and still holds its value on the other; the
// join drops that value, guarded by which branch was taken. Inside a loop,
// the guard must reflect the current iteration, not an earlier one.
fn join_drop_in_loop(n: i32) {
    let mut i = 0;
    while i < n {
        body_invariant!(i < n);
        let x = S { v: 1 };
        if i % 2 == 0 {
            consume(x);
        }
        i += 1;
    }
}

fn while_and_move(c: bool) {
    let mut x = S { v: 0 };
    while c && consume_b(x) {
        body_invariant!(true);
        x = S { v: 1 };
    }
}

fn cond_chain(c: bool, d: bool) {
    let mut x = S { v: 0 };
    while consume_b(x) && { x = S { v: 1 }; c } && d {
        body_invariant!(true);
    }
}

fn guard_then_shared_arm(k: u8, z: S) -> i32 {
    match k {
        0 if consume_b(z) => 1,
        0 | 1 | 2 => 2,
        _ => 3,
    }
}

// Each loop exit moves one of `a` and `b` and lends out the other. Assigning
// both after the loop must replace the value that is still held: adding a
// second predicate for the same place would make the path infeasible, which
// the refutation detects.
fn exits_move_or_lend(c: bool, d: bool) {
    let mut a = S { v: 1 };
    let mut b = S { v: 2 };
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
    r.v = 7;
    a = S { v: 3 };
    b = S { v: 4 };
    prusti_assert!(a.v == 3 && b.v == 4);
    prusti_refute!(false);
}
