extern crate prusti_contracts;
use prusti_contracts::*;

#[extern_spec]
impl<T> std::vec::Vec<T> {
    /// Wrong number of arguments
    #[ensures(self.len() == old(self.len()) + 1)] //~ ERROR takes 2 arguments
    fn push(&mut self);
}

fn main() {}
