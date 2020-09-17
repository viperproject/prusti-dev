/// Source: https://doc.servo.org/src/fixedbitset/lib.rs.html#18-21

#[inline]
fn div_rem(x: usize, d: usize) -> (usize, usize)
{
    (
        x / d,  //~ ERROR assertion might fail with "attempt to divide by zero"
        x % d
    )
}

fn main(){}
