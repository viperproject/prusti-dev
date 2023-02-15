use prusti_contracts::*;

#[derive(PartialEq, PartialOrd)]
struct A {
    i: i32,
}

#[extern_spec]
trait PartialOrd<Rhs> {
    #[pure]
    fn lt(&self, other: &Rhs) -> bool;
}

#[requires(_x < _y)]
fn test(_x: A, _y: A) {}

#[trusted]
fn main() {}
