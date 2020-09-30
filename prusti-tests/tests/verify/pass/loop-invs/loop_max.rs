use prusti_contracts::*;

#[requires(x > 0 && y > 0)]
#[ensures(result >= x && result >= y)]
#[ensures(result == x || result == y)]
pub fn loop_max(x: u32, y: u32) -> u32 {
    let mut r = x;
    while r < y {
        body_invariant!(x <= r && r < y);
        r += 1
    }
    r
}

fn main() {}
