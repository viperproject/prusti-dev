// compile-flags: -Punsafe_core_proof=true

#![allow(unused)]

use prusti_contracts::*;

fn main() {}

trait Trait {
    #[terminates(Int::new(x))]
    fn fun(&self, x: i64) {}
}

struct Struct;
impl Trait for Struct {
    fn fun(&self, x: i64) {
        if x > 1 {
            foo(self, x - 1);
        }
    }
}

#[terminates(Int::new(x))]
fn foo<T: Trait>(t: &T, x: i64) {
    if x > 1 {
        t.fun(x - 1);
    }
}
