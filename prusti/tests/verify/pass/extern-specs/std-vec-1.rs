#![feature(register_tool)]
#![register_tool(prusti)]

use prusti_contracts::*;

#[extern_spec]
impl<T> std::vec::Vec::<T> {
    #[ensures(result.len() == 0)]
    fn new() -> std::vec::Vec::<T>;

    #[pure]
    fn len(&self) -> usize;

    #[ensures(self.len() == old(self.len()) + 1)]
    fn push(&mut self, value: T);

    #[ensures(self.len() == 0)]
    fn clear(&mut self);
}

fn main() {
    let mut v = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    assert!(v.len() == 3);
    v.clear();
    assert!(v.len() == 0);
}
