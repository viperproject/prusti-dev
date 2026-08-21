use prusti_contracts::*;

/// Examples from Fabian Wolff's thesis.

// ignore-test
// TODO: spec entailment on `result`, the `outer` keyword, and move
// semantics for closures are not supported yet

fn main() {
    let hocl = closure!(
        #[ensures(result |= [
            ensures(result == outer(i))
        ])]
        |i: i32| {
            closure!(
                #[ensures(result == outer(i))] // ???
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
