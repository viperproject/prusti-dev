use prusti_contracts::*;

use std::marker::PhantomData;

struct Foo<A> {
    i: i32,
    x: BarBaz<A>,
}

struct BarBaz<B> {
    i: i32,
    x: PhantomData<B>,
}

#[ensures(result.i == old(arg.x.i))]
#[ensures(result.x.i == old(arg.i))]
fn test1<C, D>(arg: Foo<C>) -> Foo<D> {
    Foo {
        i: arg.x.i,
        x: BarBaz {
            i: arg.i,
            x: PhantomData,
        },
    }
}

#[ensures(result.i == old(arg.x.i))]
#[ensures(result.x.i == old(arg.i))]
fn test2(arg: Foo<u128>) -> Foo<isize> {
    let a = arg.i;
    let b = arg.x.i;
    let new = test1(arg);
    assert!(new.i == b);
    assert!(new.x.i == a);
    new
}

fn main() {}
