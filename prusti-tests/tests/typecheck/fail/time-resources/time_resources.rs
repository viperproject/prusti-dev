// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

struct MyStruct {
    time: usize,
}

#[requires(time_credits(true))] //~ ERROR mismatched types
#[ensures(time_receipts("hello"))] //~ ERROR mismatched types
fn main() {
    let mut i = 0;
    while i < 10 {
        body_invariant!(time_credits(MyStruct { time: 10 - i })); //~ ERROR mismatched types
        body_invariant!(time_receipts((i, 0))); //~ ERROR mismatched types
        i += 1;
    }
}
