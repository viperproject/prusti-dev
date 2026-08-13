use prusti_contracts::*;

pub struct S {
    v: i32,
}

fn consume(_s: S) {}

// `x` is moved out on one branch and still holds its value on the other; the
// join drops that value, guarded by which branch was taken. Inside a loop,
// the guard must reflect the current iteration, not an earlier one.
pub fn join_drop_in_loop(n: i32) {
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
