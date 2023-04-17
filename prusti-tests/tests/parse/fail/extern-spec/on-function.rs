use prusti_contracts::*;

fn identity(a: i32) -> i32 {
    a
}

#[extern_spec] // should be #[extern_spec(crate)] in this case
#[ensures(a == 0 ==> result == 0)]
fn identity(a: i32) -> i32; //~ ERROR: cannot find crate `identity` in the list of imported crates

fn main() {}
