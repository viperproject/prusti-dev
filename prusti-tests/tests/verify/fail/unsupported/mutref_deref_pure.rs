use prusti_contracts::*;

pub struct S {
    v: i32,
}

// A mutable reference's snapshot is shallow: the value behind it lives in the
// heap, so a pure function handed only the snapshot cannot read it.

#[pure]
fn get(s: &mut S) -> i32 {
    s.v //~ERROR: dereference of the mutable reference `&mut S` in pure code
}

#[pure]
fn get_nested(s: &mut &mut S) -> i32 {
    s.v //~ERROR: dereference of the mutable reference `&mut &mut S` in pure code
}

fn client(s: &mut S, t: &mut &mut S) {
    let _ = get(s);
    let _ = get_nested(t);
}
