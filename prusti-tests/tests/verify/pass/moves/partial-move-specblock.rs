use prusti_contracts::*;

fn partial_move() {
    let x = (String::new(), 5);
    let _y = x.0;
    prusti_assert!(x.1 == 5);
}

struct Inner<T>(T, i32);
struct Outer<A, B>(B, Inner<A>);

fn generic_partial_move<X, Y>(x: Outer<Y, X>) {
    let _a = x.0;
    let _b = x.1.0;
    prusti_assert!(x.1.1 + 1 - 1 == x.1.1);
}

#[requires(x.1 == 5)]
fn box_partial_move(x: Box<(String, i32)>) {
    let _y = x.0;
    prusti_assert!(x.1 == 5);
}

struct S {
    a: i32,
    b: i32,
}

#[requires(s.a == 1)]
fn intact_struct_arg(s: S) {
    prusti_assert!(s.a == 1);
}

fn nested_sibling_read() {
    let x = ((String::new(), 1), (2, 3));
    let _y = x.0.0;
    prusti_assert!(x.1.0 == 2);
}
