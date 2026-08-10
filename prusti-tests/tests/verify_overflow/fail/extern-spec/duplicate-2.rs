#![feature(allocator_api)]

use prusti_contracts::*;

#[extern_spec]
impl<T, A: std::alloc::Allocator> Vec<T, A> {
    #[trusted]
    #[pure]
    fn len(&self) -> usize;

    #[trusted]
    #[ensures(self.len() == 0)]
    fn clear(&mut self);
}

#[extern_spec]
impl<T, A: std::alloc::Allocator> Vec<T, A> {
    #[trusted]
    #[ensures(self.len() == 0)]
    fn clear(&mut self); //~ ERROR: duplicate specification for std::vec::Vec::<T, A>::clear
}

fn main() {}
