#![feature(adt_const_params)]

use std::marker::ConstParamTy;

#[derive(ConstParamTy, PartialEq, Eq)]
struct A {
    x: i32
}

impl A {
    fn foo(&self) -> i32 {
        self.x
    }
}

fn alpha<const X: A>() -> i32 {
    X.foo()
}

fn beta() {
    let x = <Bar as Foo<{A {x: 5}}>>::foo();
}

trait Foo<const X: A> {
    fn foo() -> i32;
}

struct Bar {}

impl<const X: A> Foo<X> for Bar {
    fn foo() -> i32 {
        X.x
    }
}
