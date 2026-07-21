// Coverage for `ghost!` blocks as value producers: `let x = ghost! { .. }`
// binds a `Ghost<T>` of the body's result, spec-only operations (`Int`
// comparisons, `===`, `contains`, subset tests, `Ghost` deref) are allowed
// inside the body, ghost values flow between blocks, and functions (pure and
// impure) can be called from ghost code.

use prusti_contracts::*;

// Spec-only builtins are allowed in ghost code: comparisons on `Int` yield
// real `bool`s inside the block.
fn spec_only_ops() {
    let b = ghost! {
        let b = Int::from(1) < Int::from(2);
        b
    };
    prusti_assert!(*b);
    let c = ghost! { Int::from(3) >= Int::from(4) };
    prusti_assert!(!*c);
}

// Snapshot equality (the spec-only `PartialEq` on ghost types) inside ghost
// code.
fn snap_eq() {
    let e = ghost! { seq![1, 2] == seq![1, 2] };
    prusti_assert!(*e);
}

// Spec-only collection tests inside ghost code.
fn collection_tests() {
    let t = ghost! {
        let s = set![1, 2, 3];
        let sub = set![1, 2].is_subset(s);
        let elem = s.contains(2);
        let key = map![1 => 10].contains(1);
        let inseq = seq![4, 5].contains(5);
        sub && elem && key && inseq
    };
    prusti_assert!(*t);
}

// Ghost values produced by one block are captured and used by later blocks;
// `Ghost` values deref inside ghost code.
fn value_flow() {
    let s = ghost! { seq![1, 2, 3] };
    let updated = ghost! { s.update(Int::from(0), 4) };
    let first = ghost! { *updated[Int::from(0)] };
    prusti_assert!(*first === 4);
    prusti_assert!(*updated[Int::from(2)] === 3);
}

// Runtime values are captured by reference and snapshotted.
#[requires(n < 1000)]
fn capture_runtime(n: i64) {
    let g = ghost! { Int::from(n) + Int::from(1) };
    prusti_assert!(*g <= Int::from(1000));
}

#[pure]
fn double(x: i64) -> i64 {
    x * 2
}

#[requires(x < 100)]
#[ensures(result == x + 1)]
fn incr(x: i64) -> i64 {
    x + 1
}

// Both pure and impure (contract-bearing) functions can be called in ghost
// code; locals declared inside the block can be mutated.
fn calls_in_ghost() {
    let r = ghost! {
        let mut x = double(3);
        x = incr(x);
        Int::from(x)
    };
    prusti_assert!(*r === Int::from(7));
}

// Control flow inside a ghost block.
fn branching(cond: bool) {
    let v = ghost! {
        if cond { Int::from(1) } else { Int::from(2) }
    };
    prusti_assert!(*v >= Int::from(1) && *v <= Int::from(2));
}

// A unit-valued ghost block used purely as a statement.
fn unit_block() {
    let s = seq![1, 2];
    ghost! {
        let _mid = s[Int::from(1)];
    };
}

// The ghost body runs in the enclosing frame, so it can read through
// references in scope directly.
#[requires(*r < 1000)]
fn ref_in_ghost(r: &mut i64) {
    let g = ghost! { Int::from(*r) + Int::from(1) };
    prusti_assert!(*g <= Int::from(1000));
}

// Assertions inside a ghost body are checked (and provable from facts
// established within the body).
fn assert_in_ghost(n: i64) {
    ghost! {
        let x = Int::from(2) + Int::from(2);
        prusti_assert!(x == Int::from(4));
        let y = Int::from(n);
        prusti_assert!(y * Int::from(2) == y + y);
    };
}

// Ghost blocks nest; the inner block's value flows into the outer body.
fn nested_ghost() {
    let x = ghost! {
        let inner = ghost! { Int::from(1) };
        *inner + Int::from(1)
    };
    prusti_assert!(*x === Int::from(2));
}

#[pure]
fn nested_ghost_in_pure() -> Ghost<Int> {
    ghost! {
        let inner = ghost! { Int::from(2) };
        *inner * Int::from(3)
    }
}

fn use_nested_ghost_in_pure() {
    prusti_assert!(*nested_ghost_in_pure() === Int::from(6));
}

// Loops (with body invariants) inside a ghost body.
fn loop_in_ghost() {
    let x = ghost! {
        let mut i = 0i64;
        while i < 5 {
            body_invariant!(0 <= i && i < 5);
            i += 1;
        }
        Int::from(i)
    };
    prusti_assert!(*x === Int::from(5));
}

// Ghost blocks capture generic values; the block's type follows the generic.
#[ensures(*result === x)]
fn generic_ghost<T: Copy>(x: T) -> Ghost<T> {
    let g = ghost! { x };
    prusti_assert!(*g === x);
    g
}

fn use_generic_ghost() {
    let g = generic_ghost(3u8);
    prusti_assert!(*g === 3u8);
}

// The body's type can be inferred from the binding (through `ghost_call`'s
// unification of the inline body with the `Fn`-checker closure).
fn inferred_body_type() {
    let s: Ghost<Seq<i32>> = ghost! { Seq::new() };
    prusti_assert!(s.len() === Int::from(0));
}

// Runtime-typed values can be constructed inside the ghost body.
fn aggregate_in_ghost(a: i32, b: i32) {
    let p = ghost! { (a, b) };
    prusti_assert!(*p === (a, b));
}

// `return`/`?` inside a closure nested in the ghost body exit the closure,
// not the ghost block.
fn closure_in_ghost() {
    let n = ghost! {
        let _f = |x: i32| -> Option<i32> { Some(Some(x)?) };
        let _g = || -> i32 { return 3; };
        Int::from(1)
    };
    prusti_assert!(*n === Int::from(1));
}

// Ghost blocks in pure code: the pure function's value is built from ghost
// blocks, whose bodies may use spec-only operations.
#[pure]
fn ghost_in_pure(x: i64) -> Ghost<Int> {
    ghost! { Int::from(x) + Int::from(1) }
}

#[pure]
fn ghost_branch_in_pure(cond: bool) -> Ghost<Int> {
    if cond {
        ghost! { Int::from(1) }
    } else {
        ghost! { Int::from(2) }
    }
}

#[pure]
fn ghost_cmp_in_pure(x: i64) -> Ghost<bool> {
    ghost! { Int::from(x) < Int::from(10) }
}

fn use_ghost_in_pure() {
    prusti_assert!(*ghost_in_pure(4) === Int::from(5));
    prusti_assert!(*ghost_branch_in_pure(true) === Int::from(1));
    prusti_assert!(*ghost_branch_in_pure(false) === Int::from(2));
    prusti_assert!(*ghost_cmp_in_pure(3));
}
