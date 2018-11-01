/// Issue #25 "Exhaling postconditions with `old(..)`"

extern crate prusti_contracts;

struct T {
    f: i32,
}

#[ensures="old(x.f) == result"]
fn extract(x: &mut T) -> i32 { //~ ERROR
    // move x
    let y = x;
    let mut z = T { f: 42 };
    let k = &mut z;
    k.f
    //y.f
}

fn main() {

}
