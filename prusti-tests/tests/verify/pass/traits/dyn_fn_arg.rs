use prusti_contracts::*;

trait MyTrait {}

struct S { x: i32 }

impl MyTrait for S {}

fn consume(_v: &dyn MyTrait) {}

fn consume2(_v: &mut dyn MyTrait) {}

trait Foo<X> {}

impl<X> Foo<X> for S {}

fn consume3(_v: &dyn Foo<i32>) {}

fn consume4(_v: &mut dyn Foo<u32>) {}

fn main() {
    let mut s = S { x: 42 };
    consume(&s);
    consume2(&mut s);
    consume3(&s);
    consume4(&mut s);
}

#[ensures(result == 42)] 
fn function1() -> i32 {
    let s = S { x: 42 };
    consume(&s);
    s.x
}

#[ensures(result == 42)] 
fn function2() -> i32 {
    let s = S { x: 42 };
    consume3(&s);
    s.x
}
