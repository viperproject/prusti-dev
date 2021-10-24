#![no_std]
extern crate prusti_contracts;
use prusti_contracts::*;

pub const SIZE_A: usize = core::mem::size_of::<A>();

#[derive(Clone, Copy)]
pub struct A {
    _inner: usize,
}

#[repr(transparent)]
pub struct B {
    inner: [A],
}

impl B {
    /// Bonus find related to regression test `issue-718-1`: the length of a slice reference should be at most `isize::MAX` bytes.
    /// There exists no valid way in Rust to construct slice references that span more than `isize::MAX` bytes,
    /// see <https://doc.rust-lang.org/std/slice/fn.from_raw_parts.html#safety>.
    /// In the Prusti error message for `issue-718-1`, it mentions the post-condition `result <= 18446744073709551615`.
    /// `18446744073709551615` is `usize::MAX`, which can never be valid for the length of a slice reference.
    /// (Note that raw pointers and `NonNull` do allow pointing to slices with more than `isize::MAX` bytes,
    /// this is only disallowed for references to slices, because internally the Rust core library performs
    /// "inbounds GEP" LLVM instructions on pointers derived from the slice reference.)
    #[pure]
    // FIXME: https://github.com/viperproject/prusti-dev/issues/718
    #[ensures(result.len() <= isize::MAX as usize / SIZE_A)] //~ ERROR postcondition might not hold.
    pub const fn deref(&self) -> &[A] {
        &self.inner
    }
}

fn main() {}
