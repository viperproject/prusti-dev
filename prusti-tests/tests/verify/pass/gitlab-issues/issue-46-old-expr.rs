/// Issue #46 "Field access of an old expressions"

// ignore-test: this requires encoding old expressions of type `&mut S` using snapshots

use prusti_contracts::*;

struct S {
    f: i32
}

// TODO: restore `old(x).f == 456` once `&mut` is supported in specifications;
// `old` of a `&mut` reborrows it.
#[requires(x.f == 123)]
#[ensures(old(x.f) == 123)]
#[ensures(x.f == 456)]
fn test(x: &mut S) {
    x.f = 456;
}

fn main() {}
