/// From crate `103_crossbeam-epoch`

extern crate prusti_contracts;

use std::marker::PhantomData;

pub struct Shared<'g, T: 'g> {
    data: usize,
    _marker: PhantomData<(&'g (), *const T)>,
}

/// A trait for either `Owned` or `Shared` pointers.
pub trait Pointer<T> {
    /// Returns the machine representation of the pointer.
    fn into_usize(self) -> usize;
}

impl<'g, T> Pointer<T> for Shared<'g, T> {
    #[inline]
    fn into_usize(self) -> usize {
        self.data
    }
}

fn main() {}
