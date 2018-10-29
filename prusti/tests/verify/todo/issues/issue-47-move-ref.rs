/// Issue #47 "Exhaling permission of reassigned `&mut T` argument"

extern crate prusti_contracts;

struct S {
    f: i32
}

#[requires="x.f == 123"]
#[ensures="x.f == 456"]
fn test(x: &mut S) {
    let y = S {
        f: 456
    };
    *x = y;
}

fn main() {}
