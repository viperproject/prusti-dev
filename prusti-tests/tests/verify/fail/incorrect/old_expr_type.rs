use std::marker::PhantomData;
use prusti_contracts::*;

pub struct Foo<T>(PhantomData<T>);

impl<T> Foo<T> {
    #[pure]
    #[trusted]
    pub fn len(&self) -> usize {
        unimplemented!()
    }

    #[ensures(self.len() == old(self).len() - 1)] //~ ERROR postcondition might not hold.
    pub fn foo(&mut self) -> i32 {
        42
    }
}

fn main() {}
