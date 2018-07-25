//! Example: test match expressions

extern crate prusti_contracts;

struct T {
    f: i32,
}

#[ensures="old(x.f) == x.f && x.f == result"]
fn foo(x: &mut T) -> i32 {
    x.f
}

fn main() {

}
