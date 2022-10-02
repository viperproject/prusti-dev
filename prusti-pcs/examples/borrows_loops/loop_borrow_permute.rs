extern crate prusti_contracts;
use prusti_contracts::*;

// Non-copy type
struct T {}

#[pure]
fn main() {
    let mut x: T = T {};
    let mut y: T = T {};
    let mut bt1 = &mut x;
    let mut bt2 = &mut y;
    let mut n: usize = 10;

    // Swap the loans some number of times
    while n < 20 {
        n = n + 1;
        let tmp = bt1;
        bt1 = bt2;
        bt2 = tmp;
    }

    // Force the loans to live longer than the loop (ie do the join)
    let bbx = bt1;
    let bby = bt2;

    // Force a "gradual" expiry
    let xx = x;
    let yy = y;
}

