extern crate prusti_contracts;
use prusti_contracts::*;

#[extern_spec]
impl<T> std::vec::Vec<T> {
    /// Wrong method name
    #[ensures(self.len() == 0)] //~ ERROR no function or associated item
    fn clears(&mut self);
}

fn main() {}
