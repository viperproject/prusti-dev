#![feature(register_tool)]
#![register_tool(prusti)]

extern crate prusti_contracts_internal;  // TODO: Figure out how to remove.

/*
mod foo_bar {
    pub fn x() {}
}

mod foo {

    use foo_bar::x;

    #[prusti::invariant(true)]
    struct X {}
}
*/

#[prusti::requires(x > 0)]
fn main() {
}
