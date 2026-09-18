use crate::*;
use std::vec::Vec;

#[extern_spec]
impl<T, A: core::alloc::Allocator> Vec<T, A> {
    #[trusted]
    #[pure]
    #[ensures(result == self.as_slice().len())]
    fn len(&self) -> usize;

    #[trusted]
    #[pure]
    fn as_slice(&self) -> &[T];
}
