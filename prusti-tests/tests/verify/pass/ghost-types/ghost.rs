// Coverage for the `Ghost<T>` wrapper, which is represented exactly like the
// wrapped `T`: `Ghost::new` preserves the value, distinct payloads give
// distinct ghosts, `ghost! { ... }` blocks execute in verification, and ghost
// values pass across function boundaries and wrap composite/ghost payloads.

use prusti_contracts::*;

// `Ghost::new` preserves the value; distinct payloads are distinguishable.
fn new_and_eq() {
    prusti_assert!(Ghost::new(5u32) == Ghost::new(5u32));
    // Both `T` and `&T` can be passed (`impl Value<T>`), and `new_ref` pins
    // the by-reference version; `==` on ghosts is snapshot equality.
    prusti_assert!(Ghost::new(&5u32) == Ghost::new_ref(&5u32));
    prusti_assert!(Ghost::new(5u32) != Ghost::new(10u32));
}

// A `ghost!` block produces a `Ghost` of its body's value, which can rebind
// (shadow) an earlier ghost local; the new value is observed.
fn ghost_block() {
    let x = Ghost::new(5u32);
    prusti_assert!(x == Ghost::new(5u32));
    let x = ghost! { 10u32 };
    prusti_assert!(x == Ghost::new(10u32));
}

// A ghost value crosses a function boundary through the contract, unchanged.
#[requires(g == Ghost::new(7u32))]
#[ensures(result == g)]
fn identity_ghost(g: Ghost<u32>) -> Ghost<u32> {
    g
}

fn use_boundary() {
    let r = identity_ghost(Ghost::new(7u32));
    prusti_assert!(r == Ghost::new(7u32));
}

// A ghost wrapping a composite payload; equality is structural over the tuple.
fn composite_payload() {
    let a = Ghost::new((1i32, 2i32));
    let b = Ghost::new((1i32, 2i32));
    let c = Ghost::new((1i32, 3i32));
    prusti_assert!(a == b);
    prusti_assert!(a != c);
}

// A ghost wrapping a reference type: `T = &u32` is passed directly via the
// by-value `impl Value<T> for T` (no dereference), while `&&u32` still
// dereferences one level.
fn reference_payload() {
    let r = &5u32;
    let g: Ghost<&u32> = Ghost::new(r);
    prusti_assert!(g == Ghost::new(r));
    prusti_assert!(g == Ghost::new_ref(&r));
}

// A ghost wrapping the mathematical `Int` type.
fn ghost_of_int() {
    let g = Ghost::new(Int::from(3) + Int::from(4));
    prusti_assert!(g == Ghost::new(Int::from(7)));
    prusti_assert!(g != Ghost::new(Int::from(8)));
}

// Dereferencing a ghost yields the wrapped value.
fn deref() {
    let g = Ghost::new(5u32);
    prusti_assert!(*g == 5u32);
    prusti_assert!(*Ghost::new(Int::from(3)) == Int::from(3));
}
