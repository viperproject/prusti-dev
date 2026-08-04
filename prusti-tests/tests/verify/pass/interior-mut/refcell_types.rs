// `RefCell` with different content types, generic functions, nesting, structs
// mixing `Cell` and `RefCell` fields, sharing, and the `RefCell` trait
// implementations (`Clone`, `Default`, `From`, comparisons).

use std::cell::{Cell, RefCell};

struct Pair {
    a: i32,
    b: i32,
}

fn non_copy_content() {
    let c = RefCell::new(Pair { a: 1, b: 2 });
    {
        let mut m = c.borrow_mut();
        m.a = 3;
    }
    let r = c.borrow();
    assert!(r.a == 3);
    assert!(r.b == 2);
}

fn generic_write_read<T: Copy + PartialEq>(c: &RefCell<T>, v: T) {
    {
        let mut m = c.borrow_mut();
        *m = v;
    }
    assert!(*c.borrow() == v);
}

fn generic_callers() {
    let a = RefCell::new(0u8);
    generic_write_read(&a, 5);
    let b = RefCell::new(false);
    generic_write_read(&b, true);
}

fn nested_refcell() {
    let c = RefCell::new(RefCell::new(1));
    {
        let outer = c.borrow();
        let mut inner = outer.borrow_mut();
        *inner = 2;
    }
    assert!(*c.borrow().borrow() == 2);
}

fn cell_inside_refcell() {
    let c = RefCell::new(Cell::new(1));
    {
        // Only a shared borrow is needed to mutate the inner `Cell`.
        let r = c.borrow();
        r.set(2);
    }
    assert!(c.borrow().get() == 2);
}

struct Mixed {
    counter: Cell<u32>,
    data: RefCell<i32>,
}

fn mixed_struct_through_shared_ref() {
    let m = Mixed {
        counter: Cell::new(0),
        data: RefCell::new(10),
    };
    let r = &m;
    r.counter.set(r.counter.get() + 1);
    *r.data.borrow_mut() += 1;
    assert!(r.counter.get() == 1);
    assert!(*r.data.borrow() == 11);
}

fn two_aliases_of_local() {
    let c = RefCell::new(0);
    let r1 = &c;
    let r2 = &c;
    r1.replace(1);
    assert!(*r2.borrow() == 1);
    r2.replace(2);
    assert!(*r1.borrow() == 2);
}

fn clone_is_independent() {
    let a = RefCell::new(1);
    let b = a.clone();
    *a.borrow_mut() = 5;
    assert!(*a.borrow() == 5);
    assert!(*b.borrow() == 1);
}

fn comparisons_use_contents() {
    let a = RefCell::new(1);
    let b = RefCell::new(1);
    assert!(a == b);
    b.replace(2);
    assert!(a != b);
    assert!(a < b);
    assert!(b > a);
}

fn main() {
    non_copy_content();
    generic_callers();
    nested_refcell();
    cell_inside_refcell();
    mixed_struct_through_shared_ref();
    two_aliases_of_local();
    clone_is_independent();
    comparisons_use_contents();
}
