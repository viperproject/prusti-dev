// The `RefCell` borrow flag: `try_borrow`/`try_borrow_mut` succeed or fail
// depending on which guards (`Ref`/`RefMut`) are currently alive. Proving the
// `unreachable!()` arms and the `is_ok`/`is_err` assertions requires precise
// tracking of the borrow state.

use prusti_contracts::*;
use std::cell::{Ref, RefCell};

fn free_state() {
    let c = RefCell::new(1);
    assert!(c.try_borrow().is_ok());
    assert!(c.try_borrow_mut().is_ok());
}

fn shared_state() {
    let c = RefCell::new(1);
    let r = c.borrow();
    // Another shared borrow is fine, an exclusive one is not.
    assert!(c.try_borrow().is_ok());
    assert!(c.try_borrow_mut().is_err());
    assert!(*r == 1);
    drop(r);
    assert!(c.try_borrow_mut().is_ok());
}

fn exclusive_state() {
    let c = RefCell::new(1);
    let m = c.borrow_mut();
    assert!(c.try_borrow().is_err());
    assert!(c.try_borrow_mut().is_err());
    drop(m);
    assert!(c.try_borrow().is_ok());
}

fn try_borrow_values() {
    let c = RefCell::new(41);
    match c.try_borrow() {
        Ok(r) => assert!(*r == 41),
        Err(_) => unreachable!(),
    }
    match c.try_borrow_mut() {
        Ok(mut m) => *m += 1,
        Err(_) => unreachable!(),
    }
    assert!(*c.borrow() == 42);
}

fn ref_clone_keeps_shared() {
    let c = RefCell::new(3);
    let r1 = c.borrow();
    let r2 = Ref::clone(&r1);
    assert!(*r1 == *r2);
    assert!(c.try_borrow_mut().is_err());
    drop(r1);
    // `r2` is still alive, so the cell stays shared-borrowed.
    assert!(c.try_borrow_mut().is_err());
    assert!(*r2 == 3);
    drop(r2);
    assert!(c.try_borrow_mut().is_ok());
}

fn interleaved_borrow_cycles() {
    let c = RefCell::new(0);
    let mut i = 0;
    while i < 3 {
        body_invariant!(0 <= i && i <= 3);
        // Each iteration takes and fully releases an exclusive borrow, so the
        // next iteration's `borrow_mut` cannot panic.
        let mut m = c.borrow_mut();
        *m += 1;
        drop(m);
        let r = c.borrow();
        let _v = *r;
        drop(r);
        i += 1;
    }
    assert!(c.try_borrow_mut().is_ok());
}

fn main() {
    free_state();
    shared_state();
    exclusive_state();
    try_borrow_values();
    ref_clone_keeps_shared();
    interleaved_borrow_cycles();
}
