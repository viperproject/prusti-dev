// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;


struct X {
    a: i32,
    b: i32,
    c: i32,
}

#[model]
struct X {
   a: A,
}

#[derive(Copy, Clone)]
struct Z {
    c: i32,
    b: i32,
}

#[derive(Copy, Clone)]
struct Y {
    b: Z,
}

#[derive(Copy, Clone)]
struct A {
    a: B,
}

#[derive(Copy, Clone)]
struct B {
    b: C,
}

#[derive(Copy, Clone)]
struct C{
    c: i32
}



#[ensures(x.model().a.a.b.c == 1)]
fn fail(x: X, val: i32) {
    ()
}

fn main() {}
