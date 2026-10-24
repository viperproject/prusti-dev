use prusti_contracts::*;

pub struct S {
    pub v: i32,
}

fn consume_b(_s: S) -> bool {
    true
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
