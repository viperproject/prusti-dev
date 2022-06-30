extern crate prusti_contracts;
use prusti_contracts::*;
#[ensures(result > 0)]
fn to_pos_u32(args: impl Into<u32>) -> u32 {
    let result = args.into();
    if result == 0 {
        1
    } else {
        result
    }
}

fn main() {
    let x : u16 = 5;
    let y = to_pos_u32(x);
    assert!(y > 0);
}
