// compile-flags: -Ptime_reasoning=false

use prusti_contracts::*;

// This test checks that setting the time reasoning option to false ignores timing constrains
fn sum(n: u32) -> u32 {
    let mut i = 0;
    let mut res = 0;
    while i < n {
        res += i;
        i += 1;
    }
    res
}

fn main() {
    sum(4);
}
