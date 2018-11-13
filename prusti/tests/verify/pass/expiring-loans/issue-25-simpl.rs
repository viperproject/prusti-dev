/// Issue #25 "Exhaling postconditions with `old(..)`"

extern crate prusti_contracts;

struct T {
    f: i32,
}

#[ensures="old(x.f) == result"]
fn extract(x: &mut T) -> i32 {
    x.f
}

fn main() {

}
