use prusti_contracts::*;

fn main() {
    match A::new() {
        _ => {},
    }
}

pub struct A;

pub enum E {
    Foo,
    Bar
}

impl A {
    #[trusted]
    #[ensures(matches!(result, Ok(_)) ==> matches!(result, Ok(r) if r.invariant()))]
    pub fn new() -> Result<Self, E> {
        Ok(A)
    }

    #[pure]
    #[trusted]
    pub fn invariant(&self) -> bool {
        true
    }
}
