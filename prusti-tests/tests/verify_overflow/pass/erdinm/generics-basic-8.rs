use prusti_contracts::*;

use std::marker::PhantomData;

struct Foo<A, B> {
    a: A,
    ib: Bar<B>,
    x: PhantomData<A>,
}

struct Bar<C> {
    c: C,
}

#[ensures(arg.ib.c == 42)]
fn set_a<X>(arg: &mut Foo<X, i8>) {
    arg.ib.c = 42;
}

fn test1(arg: &mut Foo<isize, i8>) {
    set_a(arg);
    assert!(arg.ib.c == 42);
}

fn main() {}
