/// Source: https://doc.servo.org/src/fixedbitset/lib.rs.html#18-21

use prusti_contracts::*;

#[inline]
fn div_rem(x: usize, d: usize) -> (usize, usize)
{
    (
        x / d,  //~ ERROR
        x % d
    )
}

fn main(){}
