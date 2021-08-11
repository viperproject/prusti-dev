extern crate prusti_contracts;
use prusti_contracts::*;

#[extern_spec]
impl<T> std::vec::Vec<T> {
    #[pure]
    fn len(&self) -> usize;

    #[ensures(self.len() == 0)]
    fn clear(&mut self);
}

#[extern_spec]
impl<T> std::vec::Vec<T> { //~ ERROR: duplicate export specification for Vec
    #[ensures(self.len() == 0)] 
    fn clear(&mut self); //~ ERROR: duplicate export specification for clear
}

fn main() {}
