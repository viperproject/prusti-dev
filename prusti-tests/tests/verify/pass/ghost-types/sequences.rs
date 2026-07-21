// Coverage for the `Seq<T>` ghost sequence type: construction (`new`/
// `single`/`append`/`seq!`), `len`, `update`, `contains`, indexing by `Int`
// (a `Ghost` element) and by ranges (subsequences), equality, and use across
// function boundaries.

use prusti_contracts::*;

// Construction and (in)equality of sequence values.
fn construction() {
    prusti_assert!(Seq::<i32>::new() == Seq::new());
    prusti_assert!(Seq::single(5) == seq![5]);
    prusti_assert!(seq![1, 2] == Seq::single(1).append(Seq::single(2)));
    prusti_assert!(Seq::<i32>::new() != seq![1]);
    prusti_assert!(seq![1, 2] != seq![2, 1]);
}

// `len` on empty, literal, and appended sequences.
fn length() {
    prusti_assert!(Seq::<i32>::new().len() == Int::from(0));
    prusti_assert!(seq![1, 2, 3].len() == Int::from(3));
    prusti_assert!(seq![7].append(seq![8, 9]).len() == Int::from(3));
}

// Indexing by `Int` yields a `Ghost` of the element, which can be compared
// by snapshot equality or dereferenced.
fn indexing() {
    let s = seq![10, 20, 30];
    prusti_assert!(s[Int::from(0)] === Ghost::new(10));
    prusti_assert!(*s[Int::from(1)] == 20);
    prusti_assert!(s[Int::from(2)] !== Ghost::new(20));
}

// Indexing by ranges yields subsequences.
fn slicing() {
    let s = seq![1, 2, 3, 4];
    prusti_assert!(s[Int::from(1)..Int::from(3)] == seq![2, 3]);
    prusti_assert!(s[Int::from(2)..] == seq![3, 4]);
    prusti_assert!(s[..Int::from(1)] == seq![1]);
}

// Indexing and slicing also accept any Rust integer (`Int: From<I>`).
fn rust_int_indexing(i: usize) {
    let s = seq![10, 20, 30];
    prusti_assert!(*s[0] == 10);
    prusti_assert!(s[2u8] === Ghost::new(30));
    prusti_assert!(s[1..3] == seq![20, 30]);
    prusti_assert!(s[2i64..] == seq![30]);
    prusti_assert!(s[..1u128] == seq![10]);
    prusti_assert!(i < 3 ==> s.contains(*s[i]));
}

// `update` replaces exactly the given index; like indexing, it accepts any
// Rust integer index (`Int: From<I>`).
fn update() {
    let s = seq![1, 2, 3].update(Int::from(1), 5);
    prusti_assert!(s == seq![1, 5, 3]);
    prusti_assert!(s.len() == Int::from(3));
    prusti_assert!(seq![1, 2, 3].update(2usize, 6) == seq![1, 2, 6]);
}

// `contains` on present and absent elements.
fn contains() {
    let s = seq![4, 5];
    // Both `T` and `&T` can be passed (`impl Value<T>`).
    prusti_assert!(s.contains(&4));
    prusti_assert!(s.contains(5));
    prusti_assert!(!s.contains(&6));
}

// A sequence as a pure-function argument, related in the contract.
#[pure]
#[requires(s.len() >= Int::from(1))]
#[ensures(result === s[Int::from(0)])]
fn first(s: Seq<i32>) -> Ghost<i32> {
    s[Int::from(0)]
}

fn use_boundary() {
    let s = seq![41, 42];
    prusti_assert!(*first(s) == 41);
}
