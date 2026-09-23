// ignore-test: `replace_with` takes a closure, which needs closure
// specification support (pending).

// Closure-taking `RefCell` methods.

use std::cell::RefCell;

fn replace_with_uses_old() {
    let c = RefCell::new(5);
    let old = c.replace_with(|v| *v + 1);
    assert!(old == 5);
    assert!(*c.borrow() == 6);
}

fn main() {
    replace_with_uses_old();
}
