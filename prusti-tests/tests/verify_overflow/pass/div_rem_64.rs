/// From time::duration[0]::div_rem_64[0]

use prusti_contracts::*;

#[requires(other != 0 && other != -1)]
fn div_rem_64(this: i64, other: i64) -> (i64, i64) {
    (this / other, this % other)
}


fn main() {}
