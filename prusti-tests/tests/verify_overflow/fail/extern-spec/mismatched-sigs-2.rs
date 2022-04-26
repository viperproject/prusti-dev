extern crate prusti_contracts;
use prusti_contracts::*;

#[extern_spec]
impl<T> std::vec::Vec<T> {
    /// Wrong method name
    #[ensures(self.len() == 0)]
    fn clears(&mut self); //~ ERROR no function or associated item
}

fn main() {}
