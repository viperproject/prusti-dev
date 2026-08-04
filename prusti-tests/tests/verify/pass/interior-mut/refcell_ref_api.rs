// The `Ref` and `RefMut` guard APIs: `map`, `map_split`, `filter_map` and
// `Ref::clone`, including writes through mapped `RefMut`s.

use std::cell::{Ref, RefCell, RefMut};

fn ref_map_projects_field() {
    let c = RefCell::new((1, 2));
    let first = Ref::map(c.borrow(), |t| &t.0);
    assert!(*first == 1);
}

fn ref_map_split() {
    let c = RefCell::new((1, 2));
    let (a, b) = Ref::map_split(c.borrow(), |t| (&t.0, &t.1));
    assert!(*a == 1);
    assert!(*b == 2);
}

fn ref_filter_map_ok() {
    let c = RefCell::new(5);
    let res = Ref::filter_map(c.borrow(), |v| if *v > 0 { Some(v) } else { None });
    match res {
        Ok(r) => assert!(*r == 5),
        Err(_) => unreachable!(),
    }
}

fn ref_filter_map_err_returns_original() {
    let c = RefCell::new(-1);
    let res = Ref::filter_map(c.borrow(), |v| if *v > 0 { Some(v) } else { None });
    match res {
        Ok(_) => unreachable!(),
        Err(orig) => assert!(*orig == -1),
    }
}

fn refmut_map_writes_through() {
    let c = RefCell::new((1, 2));
    {
        let mut first = RefMut::map(c.borrow_mut(), |t| &mut t.0);
        *first = 10;
    }
    let r = c.borrow();
    assert!(r.0 == 10);
    assert!(r.1 == 2);
}

fn refmut_map_split_disjoint_writes() {
    let c = RefCell::new((1, 2));
    {
        let (mut a, mut b) = RefMut::map_split(c.borrow_mut(), |t| (&mut t.0, &mut t.1));
        *a += 1;
        *b += 1;
    }
    let r = c.borrow();
    assert!(r.0 == 2);
    assert!(r.1 == 3);
}

fn refmut_filter_map_ok() {
    let c = RefCell::new(5);
    let res = RefMut::filter_map(c.borrow_mut(), |v| if *v > 0 { Some(v) } else { None });
    match res {
        Ok(mut m) => *m = 6,
        Err(_) => unreachable!(),
    }
    assert!(*c.borrow() == 6);
}

// A mapped guard keeps the whole cell borrowed.
fn mapped_guard_holds_borrow() {
    let c = RefCell::new((1, 2));
    let first = Ref::map(c.borrow(), |t| &t.0);
    assert!(c.try_borrow_mut().is_err());
    drop(first);
    assert!(c.try_borrow_mut().is_ok());
}

fn main() {
    ref_map_projects_field();
    ref_map_split();
    ref_filter_map_ok();
    ref_filter_map_err_returns_original();
    refmut_map_writes_through();
    refmut_map_split_disjoint_writes();
    refmut_filter_map_ok();
    mapped_guard_holds_borrow();
}
