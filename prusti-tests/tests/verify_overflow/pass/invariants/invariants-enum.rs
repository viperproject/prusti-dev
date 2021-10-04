extern crate prusti_contracts;
use prusti_contracts::*;

#[invariant(self.f < 10)]
struct Foo { f: u32 }

struct Baz { g: u32 }

enum Bar {
    Foo1(Foo), Foo2(u32)
}

#[ensures(result < 20)]
fn go(bar: Bar) -> u32 {
   match bar {
       Bar::Foo1(f) => f.f,
       Bar::Foo2(_) => 2
   }
}

fn main(){

}
