extern crate prusti_contracts;
use prusti_contracts::*;

pub trait Max {
    fn max(&mut self) -> i32;
}

pub struct Point(pub i32, pub i32);

impl Max for Point {
    fn max(&mut self) -> i32 {
        if self.0 > self.1 {
            self.0
        } else {
            self.1
        }
    }
}

#[extern_spec]
impl Point {
    #[pure]
    #[ensures(result >= self.0 && result >= self.1)]
    #[ensures(result == self.0 || result == self.1)]
    fn max(&mut self) -> i32;   //~ ERROR: pure function parameters must be Copy
}

fn main() {
    let mut ts = Point(3, 2);
    let x = ts.max();   //~ ERROR: precondition of pure function call might not hold
    assert!(x == 3)
}
