extern crate prusti_contracts;
use prusti_contracts::*;

pub trait Max {
    fn max(&self) -> i32;
}

pub struct Point(pub i32, pub i32);

impl Max for Point {
    fn max(&self) -> i32 {
        if self.0 > self.1 {
            self.0
        } else {
            self.1
        }
    }
}

#[extern_spec]
impl Max for Point {
    #[pure]
    #[ensures(result >= self.0 && result >= self.1)]
    #[ensures(result == self.0 || result == self.1)]
    fn max(&self) -> i32;
}

fn main() {
    let ts = Point(3, 2);
    let x = ts.max();
    assert!(x == 3)
}
