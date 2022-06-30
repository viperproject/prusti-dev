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
    let x1 : u16 = 5;
    let y1 = to_pos_u32(x1);
    assert!(y1 > 0);
    let x2 : u8 = 5;
    let y2 = to_pos_u32(x2);
    assert!(y2 > 0);
}
