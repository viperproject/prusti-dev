use prusti_contracts::*;

// A specification reads a referent from the heap, which needs an address
// holding a predicate; one it borrowed itself has none.

#[requires(match x {
    Some(v) => *v > 0,
    //~^ ERROR mutable borrow of `i32` in a specification
    None => true,
})]
fn match_binding(x: &mut Option<i32>) {}

#[requires({ let v = &mut 10; *v == 10 })]
//~^ ERROR mutable borrow of `i32` in a specification
fn fresh_borrow() {}
