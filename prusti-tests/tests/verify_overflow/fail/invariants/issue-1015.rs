// compile-flags: -Penable_type_invariants=true
use prusti_contracts::*;

#[invariant(false)]
struct S;

#[pure]
#[ensures(false)] //~ ERROR postcondition might not hold.
fn foo(s: &S) {}

fn main() {
    let s = S;
    foo(&s);
    assert!(false);
}
