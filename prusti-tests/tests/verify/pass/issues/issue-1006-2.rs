// ignore-test re-enable with snapshot equality (merge #980)

use std::marker::PhantomData;

use prusti_contracts::*;

fn main() {}

/// A [GhostBox] is a "pure" zero-sized owned pointer to some type
/// that must implement the `Copy` trait, it can be used
/// to build recursive (and/or zero sized) ghost ADTs.
#[derive(Copy, Clone)]
pub struct GhostBox<T: Copy>(PhantomData<T>);

#[refine_trait_spec]
impl<T: Copy + PartialEq> PartialEq for GhostBox<T> {
    #[pure]
    fn eq(&self, other: &Self) -> bool {
        self.get() == other.get()
    }

    #[pure]
    fn ne(&self, other: &Self) -> bool {
        self.get() != other.get()
    }
}

impl<T: Copy + PartialEq + Eq> Eq for GhostBox<T> {}

/// Implement `Deref` for easy access to the inner contents.
#[refine_trait_spec]
impl<T: Copy> core::ops::Deref for GhostBox<T> {
    type Target = T;

    #[pure]
    #[trusted]
    #[ensures(*result === GhostBox::get(*self))]
    fn deref(&self) -> &Self::Target {
        unreachable!()
    }
}

impl<T: Copy> GhostBox<T> {
    /// Obtain the contents of the [GhostBox].
    #[pure]
    #[trusted]
    pub const fn get(self) -> T {
        unreachable!()
    }
}

/// Snapshot equality would be enough to construct the [GhostBox],
/// the `PartialEq + Eq` trait bounds are not really needed here.
impl<T: Copy + PartialEq + Eq> GhostBox<T> {
    /// Construct a new [GhostBox].
    #[pure]
    #[trusted]
    #[ensures(result.get() == inner)]
    #[allow(unused_variables)]
    pub const fn new(inner: T) -> Self {
        Self(PhantomData)
    }
}

#[pure]
pub fn foo() -> GhostBox<i64> {
    GhostBox::new(1)
}

#[pure]
fn bar() {
    let a = &foo();
    a.get();
}
