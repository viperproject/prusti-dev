//! Example: drop a field of a struct

extern crate prusti_contracts;

struct A;
struct B {
    a1: A,
    a2: A
}
struct C {
    b: B
}
struct D {
    c: C
}

fn drop(a: A) {}

fn main() {
    let a1 = A;
    let a2 = A;
    let b = B { a1, a2 };
    let c = C { b };
    let d = D { c };

    drop(d.c.b.a1); // drop sub-field

    let x = d.c.b.a2; // still accessible
}
