use prusti_contracts::*;

#[derive(PartialEq, Eq)]
struct A { x: usize }

#[requires(forall(|other: A| _foo == other))]
fn test(_foo: A) {}

#[requires(forall(|other: u32| _foo == other))]
fn test2(_foo: u32) {}

fn main() {}
