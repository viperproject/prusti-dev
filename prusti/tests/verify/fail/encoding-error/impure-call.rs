extern crate prusti_contracts;

fn get_u32() -> u32 {
    123
}

#[requires="get_u32() == 123"]
//~^ ERROR use of impure function "get_u32" in assertion
//~^^ ERROR use of impure function might be reachable.
fn client_1() {}

#[requires="if false { get_u32() == 123 } else { 1 == 1 }"]
//~^ ERROR use of impure function "get_u32" in assertion
fn client_2() {}

fn main() {}
