#![feature(stmt_expr_attributes)]

use prusti_contracts::*;

/// Examples from Fabian Wolff's thesis.

// ignore-test
// TODO: return type for the nested closure cannot be written, but is required
// in the spec entailment
// TODO: outer keyword
// TODO: move semantics for closures

fn main() {
    let hocl = closure!(
        ensures(result |= [
            ensures(result == outer(i))
        ]),
        |i: i32| {
            closure!(
                ensures(result == outer(i)), // ???
                move || i
            )
        }
    );
    let mut f = hocl(1);
    assert_eq!(f(), 1);

    let g = hocl(2);
    assert!(f() != g());

    f = g;
    assert_eq!(f(), g());
}
