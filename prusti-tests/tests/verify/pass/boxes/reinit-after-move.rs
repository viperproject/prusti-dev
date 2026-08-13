use prusti_contracts::*;

pub struct S {
    v: i32,
}

fn consume(_s: S) {}

// Moving out of a box keeps its allocation, which `*b = ..` then reuses.
pub fn reinit_after_move() {
    let mut b = Box::new(S { v: 1 });
    let s = *b;
    *b = S { v: 5 };
    prusti_assert!(b.v == 5);
    consume(s);
}

pub fn cond_reinit(c: bool) {
    let mut b = Box::new(S { v: 1 });
    if c {
        let s = *b;
        consume(s);
        *b = S { v: 2 };
    }
    prusti_assert!(b.v == 1 || b.v == 2);
}
