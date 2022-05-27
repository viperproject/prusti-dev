#![feature(allocator_api)]

use prusti_contracts::*;

#[extern_spec]
impl<T, A: std::alloc::Allocator> Vec<T, A> {
    #[pure]
    fn len(&self) -> usize;

    #[ensures(self.len() == 0)]
    fn clear(&mut self);
}

#[extern_spec]
impl<T, A: std::alloc::Allocator> Vec<T, A> {
    #[ensures(self.len() == 0)]
    fn clear(&mut self); //~ ERROR: duplicate specification for std::vec::Vec::<T, A>::clear
}

fn main() {}
