// Basic `std::cell::RefCell` API: construction, dynamic borrows, writes and
// consumption. All borrows are provably disjoint, so no `borrow`/`borrow_mut`
// call can panic and all assertions hold.

use std::cell::RefCell;

fn new_and_borrow() {
    let c = RefCell::new(5);
    let r = c.borrow();
    assert!(*r == 5);
}

fn borrow_mut_writes() {
    let c = RefCell::new(0);
    {
        let mut m = c.borrow_mut();
        *m = 7;
        assert!(*m == 7);
    }
    assert!(*c.borrow() == 7);
}

fn multiple_shared_borrows() {
    let c = RefCell::new(5);
    let r1 = c.borrow();
    let r2 = c.borrow();
    assert!(*r1 == 5);
    assert!(*r2 == 5);
    assert!(*r1 == *r2);
}

fn sequential_borrows() {
    let c = RefCell::new(1);
    let r = c.borrow();
    assert!(*r == 1);
    drop(r);
    let mut m = c.borrow_mut();
    *m += 1;
    drop(m);
    assert!(*c.borrow() == 2);
}

fn replace_returns_old() {
    let c = RefCell::new(5);
    let old = c.replace(10);
    assert!(old == 5);
    assert!(*c.borrow() == 10);
}

fn replace_with_uses_old() {
    let c = RefCell::new(5);
    let old = c.replace_with(|v| *v + 1);
    assert!(old == 5);
    assert!(*c.borrow() == 6);
}

fn swap_distinct() {
    let a = RefCell::new(1);
    let b = RefCell::new(2);
    a.swap(&b);
    assert!(*a.borrow() == 2);
    assert!(*b.borrow() == 1);
}

fn take_leaves_default() {
    let c = RefCell::new(7);
    let v = c.take();
    assert!(v == 7);
    assert!(*c.borrow() == 0);
}

fn into_inner_returns_value() {
    let c = RefCell::new(3);
    c.replace(4);
    assert!(c.into_inner() == 4);
}

fn get_mut_unique_access() {
    let mut c = RefCell::new(1);
    *c.get_mut() = 9;
    assert!(*c.borrow() == 9);
}

fn as_ptr_does_not_change_value() {
    let c = RefCell::new(1);
    let _p = c.as_ptr();
    assert!(*c.borrow() == 1);
}

fn default_is_default() {
    let c: RefCell<i32> = RefCell::default();
    assert!(*c.borrow() == 0);
}

fn from_value() {
    let c = RefCell::from(8);
    assert!(*c.borrow() == 8);
}

fn main() {
    new_and_borrow();
    borrow_mut_writes();
    multiple_shared_borrows();
    sequential_borrows();
    replace_returns_old();
    replace_with_uses_old();
    swap_distinct();
    take_leaves_default();
    into_inner_returns_value();
    get_mut_unique_access();
    as_ptr_does_not_change_value();
    default_is_default();
    from_value();
}
