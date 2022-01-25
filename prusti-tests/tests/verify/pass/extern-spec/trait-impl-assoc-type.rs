extern crate prusti_contracts;
use prusti_contracts::*;

trait Incrementable {
    type Result;
    fn increment(&mut self) -> Self::Result;
}

struct Number(i32);

impl Incrementable for Number {
    fn increment(&mut self) {
        self.0 += 1;
    }
}

#[extern_spec]
impl Incrementable for Number {
    type Result = i32;
    #[ensures( self.0 == old(self.0) + 1 )]
    #[ensures( result == self.0 )]
    fn increment(&mut self) -> i32;
}

fn main() {
    let mut num = Number { 0: 0 };
    let res = num.increment();
    assert!(num.0 == 1);
    assert!(res == 1);
    let res = num.increment();
    assert!(num.0 == 2);
    assert!(res == 2);
}