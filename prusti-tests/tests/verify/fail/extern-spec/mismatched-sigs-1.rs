extern crate prusti_contracts;
use prusti_contracts::*;

#[extern_spec]
impl<T> std::vec::Vec<T> {
    /// Wrong number of arguments
    #[ensures(self.len() == old(self.len()) + 1)]
    fn push(&mut self); //~ ERROR this function takes 2 arguments but 1 argument was supplied
}

fn main() {}
