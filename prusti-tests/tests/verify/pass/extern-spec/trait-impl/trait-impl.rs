extern crate prusti_contracts;
use prusti_contracts::*;

trait Incrementable {
    fn increment(&mut self);
}

struct Number(i32);

impl Incrementable for Number {
    fn increment(&mut self) {
        self.0 += 1;
    }
}

#[extern_spec]
impl Incrementable for Number {
    #[ensures( self.0 == old(self.0) + 1 )]
    fn increment(&mut self);
}

fn main() {
    let mut num = Number { 0: 0 };
    num.increment();
    assert!(num.0 == 1);
    num.increment();
    assert!(num.0 == 2);
}