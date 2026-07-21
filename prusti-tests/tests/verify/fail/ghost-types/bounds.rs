// In impure (ghost) code the partial collection operations are *checked*:
// out-of-bounds indexing/updating and lookups of absent keys are
// verification errors (in specs they are underspecified instead, since the
// snapshot functions carry no preconditions).

use prusti_contracts::*;

fn oob_index() {
    ghost! {
        let s = seq![1, 2];
        let _x = s[Int::from(5)]; //~ERROR: the sequence index may be out of bounds
    };
}

fn oob_update() {
    ghost! {
        let s = seq![1, 2];
        let _s2 = s.update(Int::from(5), 3); //~ERROR: the update index may be out of bounds
    };
}

fn missing_key() {
    ghost! {
        let m = map![1 => 10];
        let _v = m[2]; //~ERROR: the map may not contain this key
    };
}

fn oob_slice() {
    ghost! {
        let s = seq![1, 2];
        let _s2 = s[Int::from(0)..Int::from(100)]; //~ERROR: the range bounds may be out of bounds
    };
}

fn oob_slice_from() {
    ghost! {
        let s = seq![1, 2];
        let _s2 = s[Int::from(3)..]; //~ERROR: the range bounds may be out of bounds
    };
}

// Rust-integer indices (`Int: From<I>`) are checked the same way.
fn oob_index_rust_int() {
    ghost! {
        let s = seq![1, 2];
        let _x = s[5usize]; //~ERROR: the sequence index may be out of bounds
    };
}

// Possibly-negative indices are reported distinctly from too-large ones.
fn negative_index() {
    ghost! {
        let s = seq![1, 2];
        let _x = s[Int::from(0) - Int::from(1)]; //~ERROR: the sequence index may be negative
    };
}

fn negative_update() {
    ghost! {
        let s = seq![1, 2];
        let _s2 = s.update(-Int::from(1), 3); //~ERROR: the update index may be negative
    };
}

// Each call site is keyed (and reported) separately: with an in-bounds access
// on the line before, the error must point at the *second* access.
fn oob_second_access() {
    ghost! {
        let s = seq![1, 2];
        let _a = s[Int::from(0)];
        let _b = s[Int::from(9)]; //~ERROR: the sequence index may be out of bounds
    };
}
