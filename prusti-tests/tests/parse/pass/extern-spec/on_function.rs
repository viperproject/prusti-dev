use prusti_contracts::*;

fn identity(a: i32) -> i32 {
    a
}

#[extern_spec]
#[ensures(a == 0 ==> result == 0)]
fn identity(a: i32) -> i32;

fn main() {
}
