/// Issue #25 "Exhaling postconditions with `old(..)`"

use prusti_contracts::*;

struct T {
    f: i32,
}

#[ensures(old(x.f) == result)]
fn extract(x: &mut T) -> i32 {
    x.f
}

fn main() {

}
