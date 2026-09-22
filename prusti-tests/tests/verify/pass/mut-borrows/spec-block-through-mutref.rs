use prusti_contracts::*;

pub struct S {
    v: i32,
}

// A mutable reference's referent lives in the heap rather than in its
// snapshot, so a spec block reads it from there like a pre/postcondition does.

#[requires(s.v == 5)]
#[ensures(s.v == 5)]
fn untouched(s: &mut S) {
    prusti_assert!(s.v == 5);
}

#[requires(s.v == 5)]
#[ensures(s.v == 6)]
fn bumped(s: &mut S) {
    prusti_assert!(s.v == 5);
    s.v += 1;
    prusti_assert!(s.v == 6);
}

#[requires(s.v == 5)]
fn through_a_reborrow(s: &mut S) {
    let r = &mut *s;
    prusti_assert!(r.v == 5);
}

fn shared_reborrow_in_a_match(x: &mut Option<i32>) {
    let r = &mut *x;
    prusti_assert!(match &*r {
        Some(v) => *v == *v,
        None => true,
    });
}
