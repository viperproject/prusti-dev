extern crate prusti_contracts;
use prusti_contracts::*;

use std::collections::LinkedList;

#[extern_spec]
impl LinkedList::<i32> {
    #[ensures(true)]
    pub fn new() -> LinkedList<i32>;
}

#[extern_spec]
impl<T> LinkedList<T> {
    #[ensures(true)]
    pub fn new() -> LinkedList<T>; //~ ERROR duplicate specification
}

fn main() {
    let mut f = LinkedList::new();
    f.push_back(3);
}
