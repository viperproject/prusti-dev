use prusti_contracts::*;

#[derive(PartialEq, PartialOrd)]
struct A {
    i: i32,
}

#[extern_spec]
trait PartialOrd<#[generic] Rhs> {
    #[pure]
    fn lt(&self, other: &Rhs) -> Option<std::cmp::Ordering>;
}

#[requires(_x < _y)]
fn test(_x: A, _y: A) {}

#[trusted]
fn main() {}
