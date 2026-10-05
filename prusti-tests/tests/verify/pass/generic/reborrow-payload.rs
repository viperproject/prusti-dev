use prusti_contracts::*;

// A reborrow rebuilds the referent's snapshot from its concrete value.

#[ensures(result === x)]
fn reborrow<T>(x: &T) -> &T {
    &*x
}

#[derive(Clone, Copy)]
struct S {
    f: u32,
}

#[ensures(result === x)]
fn reborrow_concrete(x: &S) -> &S {
    &*x
}

#[requires(x.f == 3)]
fn client(x: &S) {
    let r = reborrow(x);
    let r2: &S = &*r;
    prusti_assert!(r2 === x);
    assert!(r2.f == 3);
}
