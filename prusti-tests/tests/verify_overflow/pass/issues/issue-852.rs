use prusti_contracts::*;

pub struct Bar {
    val: bool,
}

#[requires(bar.val && pred(bar))]
fn foo(bar: &Bar) {}

predicate! {
    pub fn pred(bar: &Bar) -> bool {
        true
    }
}

fn main() {}
