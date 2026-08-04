// Sharing and aliasing of `Cell`s: writes through one alias are visible
// through all others, and functions taking several `&Cell` parameters must
// only assert facts that also hold when the parameters alias.

use prusti_contracts::*;
use std::cell::Cell;

fn two_aliases_of_local() {
    let c = Cell::new(0);
    let r1 = &c;
    let r2 = &c;
    r1.set(1);
    assert!(r2.get() == 1);
    r2.set(2);
    assert!(r1.get() == 2);
    assert!(c.get() == 2);
}

// `a` and `b` may alias, so after both writes only the second is known.
fn last_write_wins(a: &Cell<i32>, b: &Cell<i32>) {
    a.set(1);
    b.set(2);
    assert!(b.get() == 2);
}

// Reading through one reference does not change what the other refers to.
fn reads_do_not_interfere(a: &Cell<i32>, b: &Cell<i32>) {
    a.set(3);
    let _ = b.get();
    assert!(a.get() == 3);
}

// `Cell::swap` is specified for aliased arguments too (it is a no-op then),
// so this postcondition-style assertion holds either way.
fn swap_may_alias(a: &Cell<i32>, b: &Cell<i32>) {
    let va = a.get();
    let vb = b.get();
    a.swap(b);
    assert!(a.get() == vb);
    assert!(b.get() == va);
}

fn callers() {
    let c = Cell::new(0);
    let d = Cell::new(9);
    last_write_wins(&c, &c);
    last_write_wins(&c, &d);
    reads_do_not_interfere(&c, &c);
    reads_do_not_interfere(&c, &d);
    swap_may_alias(&c, &c);
    swap_may_alias(&c, &d);
}

fn loop_with_invariant() {
    let c = Cell::new(0);
    let mut i = 0;
    while i < 10 {
        body_invariant!(0 <= i && i <= 10);
        body_invariant!(c.get() == i);
        c.set(c.get() + 1);
        i += 1;
    }
    assert!(c.get() == 10);
}

struct Counter {
    count: Cell<u32>,
}

// A shared counter mutated through a shared reference.
fn counter_through_shared_ref() {
    let counter = Counter {
        count: Cell::new(0),
    };
    let c = &counter;
    c.count.set(c.count.get() + 1);
    c.count.set(c.count.get() + 1);
    assert!(c.count.get() == 2);
    assert!(counter.count.get() == 2);
}

fn main() {
    two_aliases_of_local();
    callers();
    loop_with_invariant();
    counter_through_shared_ref();
}
