// User-written contracts over `Cell` contents: pre/postconditions that
// mention `Cell::get`, including two-state (`old`) postconditions, and
// callers relying on them.

use prusti_contracts::*;
use std::cell::Cell;

#[ensures(c.get() == v)]
fn set_cell(c: &Cell<i32>, v: i32) {
    c.set(v);
}

#[ensures(result == c.get())]
fn read_cell(c: &Cell<i32>) -> i32 {
    c.get()
}

#[ensures(c.get() == old(c.get()) + 1)]
#[ensures(result == c.get())]
fn increment(c: &Cell<i32>) -> i32 {
    c.set(c.get() + 1);
    c.get()
}

#[requires(c.get() > 0)]
#[ensures(c.get() == old(c.get()) - 1)]
fn decrement_positive(c: &Cell<i32>) {
    c.set(c.get() - 1);
}

fn client() {
    let c = Cell::new(0);
    set_cell(&c, 5);
    assert!(c.get() == 5);
    let v = read_cell(&c);
    assert!(v == 5);
    let w = increment(&c);
    assert!(w == 6);
    assert!(c.get() == 6);
    decrement_positive(&c);
    assert!(c.get() == 5);
}

struct Counter {
    count: Cell<u32>,
}

impl Counter {
    #[ensures(result.count.get() == 0)]
    fn new() -> Self {
        Counter {
            count: Cell::new(0),
        }
    }

    #[ensures(self.count.get() == old(self.count.get()) + 1)]
    #[ensures(result == self.count.get())]
    fn increment(&self) -> u32 {
        let n = self.count.get() + 1;
        self.count.set(n);
        n
    }
}

fn counter_client() {
    let counter = Counter::new();
    let a = counter.increment();
    assert!(a == 1);
    let b = counter.increment();
    assert!(b == 2);
    assert!(counter.count.get() == 2);
}

fn main() {
    client();
    counter_client();
}
