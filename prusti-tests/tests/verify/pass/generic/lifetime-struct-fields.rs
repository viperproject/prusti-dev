// Regression test for IndirectPredicatesEnc handling of lifetime-annotated
// struct fields: direct lifetime on field, and no lifetime on field.
use prusti_contracts::*;

// Case 1: direct lifetime argument on field.
struct Wrapper<'a> {
    x: &'a i32,
}

#[ensures(result.x === x)]
fn wrap(x: &i32) -> Wrapper<'_> {
    Wrapper { x }
}

#[ensures(result == 42)]
fn client_wrap() -> i32 {
    let val = 42;
    let w = wrap(&val);
    *w.x
}

// Case 2: no lifetime argument on field (mixed struct).
struct Mixed<'a> {
    reference: &'a i32,
    boxed: Box<i32>,
}

#[ensures(result.reference === x && *result.boxed == 42)]
fn make_mixed(x: &i32) -> Mixed<'_> {
    Mixed { boxed: Box::new(42), reference: x }
}

#[ensures(result == 42)]
fn client_mixed() -> i32 {
    let val = 0;
    let m = make_mixed(&val);
    *m.boxed
}

// Case 3: indirect lifetime argument on field (lifetime through type argument).
struct Indirect<'a> {
    boxed: Box<&'a i32>,
}

#[ensures(*result.boxed === x)]
fn make_indirect(x: &i32) -> Indirect<'_> {
    Indirect { boxed: Box::new(x) }
}

#[ensures(result == 42)]
fn client_indirect() -> i32 {
    let val = 42;
    let m = make_indirect(&val);
    *(*m.boxed)
}

fn main() {
    let _ = client_wrap();
    let _ = client_mixed();
    let _ = client_indirect();
}
