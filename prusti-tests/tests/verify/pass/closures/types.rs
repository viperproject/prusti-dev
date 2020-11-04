#![feature(stmt_expr_attributes)]

use prusti_contracts::*;

// ignore-test
// TODO: support non-i32 types in closures

struct Foo {
    foo: usize
}

enum Bar {
    Bar(x: usize)
}

fn main() {
    let f1 = closure!(
        requires(i >= 0),
        ensures(result == 1),
        |i: i32| -> i32 { 1 }
    );
    f1(0);

    let f2 = closure!(
        requires(i),
        ensures(result == 1),
        |i: bool| -> i32 { 1 }
    );
    f2(true);

    let f3 = closure!(
        requires(i >= 10),
        ensures(result == 1),
        |i: usize| -> i32 { 1 }
    );
    f3(10);

    let f4 = closure!(
        requires(i.foo >= 10),
        ensures(result == 1),
        |i: Foo| -> i32 { 1 }
    );
    f4(Foo { foo: 10 });

    let f5 = closure!(
        requires(matches!(i, Bar::Bar(x) if x >= 10)),
        ensures(result == 1),
        |i: Bar| -> i32 { 1 }
    );
    f5(Bar::Bar(10));
}
