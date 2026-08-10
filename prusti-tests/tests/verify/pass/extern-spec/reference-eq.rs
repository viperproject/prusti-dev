//! The `extern_spec`s for `PartialEq` between references relate equality of
//! references to equality of their referents, so `==` and `!=` can be moved
//! through a reference. Covers each combination of `&`/`&mut` on either side.

use prusti_contracts::*;

fn shared_shared(x: &i32, y: &i32) {
    prusti_assert!((x == y) == (*x == *y));
    prusti_assert!((x != y) == (*x != *y));
}

fn unique_unique(x: &mut i32, y: &mut i32) {
    prusti_assert!((x == y) == (*x == *y));
    prusti_assert!((x != y) == (*x != *y));
}

fn shared_unique(x: &i32, y: &mut i32) {
    prusti_assert!((x == y) == (*x == *y));
    prusti_assert!((x != y) == (*x != *y));
}

fn unique_shared(x: &mut i32, y: &i32) {
    prusti_assert!((x == y) == (*x == *y));
    prusti_assert!((x != y) == (*x != *y));
}

fn main() {
    let (mut a, mut b) = (1i32, 2i32);
    shared_shared(&a, &b);
    shared_unique(&a, &mut b);
    unique_shared(&mut a, &b);
    unique_unique(&mut a, &mut b);
}
