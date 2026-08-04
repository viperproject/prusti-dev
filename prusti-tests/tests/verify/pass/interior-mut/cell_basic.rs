// Basic `std::cell::Cell` API: construction, reads, writes and consumption.
// All assertions hold in every execution; a future Prusti with fully
// specified `Cell` methods should verify this file.

use std::cell::Cell;

fn new_and_get() {
    let c = Cell::new(42);
    assert!(c.get() == 42);
}

fn set_overwrites() {
    let c = Cell::new(0);
    c.set(1);
    assert!(c.get() == 1);
    c.set(2);
    assert!(c.get() == 2);
}

fn replace_returns_old() {
    let c = Cell::new(5);
    let old = c.replace(10);
    assert!(old == 5);
    assert!(c.get() == 10);
}

fn swap_distinct() {
    let a = Cell::new(1);
    let b = Cell::new(2);
    a.swap(&b);
    assert!(a.get() == 2);
    assert!(b.get() == 1);
}

fn take_leaves_default() {
    let c = Cell::new(7);
    let v = c.take();
    assert!(v == 7);
    assert!(c.get() == 0);
}

fn into_inner_returns_value() {
    let c = Cell::new(3);
    c.set(4);
    assert!(c.into_inner() == 4);
}

fn get_mut_unique_access() {
    let mut c = Cell::new(1);
    *c.get_mut() = 9;
    assert!(c.get() == 9);
}

fn from_mut_view() {
    let mut x = 3;
    let c = Cell::from_mut(&mut x);
    c.set(4);
    assert!(c.get() == 4);
    assert!(x == 4);
}

fn as_ptr_does_not_change_value() {
    let c = Cell::new(1);
    let _p = c.as_ptr();
    assert!(c.get() == 1);
}

fn main() {
    new_and_get();
    set_overwrites();
    replace_returns_old();
    swap_distinct();
    take_leaves_default();
    into_inner_returns_value();
    get_mut_unique_access();
    from_mut_view();
    as_ptr_does_not_change_value();
}
