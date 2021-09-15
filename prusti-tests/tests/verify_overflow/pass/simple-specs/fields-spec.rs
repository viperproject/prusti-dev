//! Example: test encoding of fields in specifications

use prusti_contracts::*;

struct S {
    a: i32,
    b: i32
}

#[requires(x.0 == 123 && x.1 == 42)]
#[ensures(result.0 == 42 && result.1 == 123)]
fn test_tuple_field(x: (i32, i32)) -> (i32, i32) {
    (x.1, x.0)
}

#[requires(x.a == 123 && x.b == 42)]
#[ensures(result.a == 42 && result.b == 123)]
fn test_struct_field(x: S) -> S {
    S {
        a: x.b,
        b: x.a
    }
}

fn main() {

}
