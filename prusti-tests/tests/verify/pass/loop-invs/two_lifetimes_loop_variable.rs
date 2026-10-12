// The loop-carried `c` has two lifetimes (`&'?1 &'?2 i32`); encoding the
// loop invariant needs the projections of both.
fn two_lifetimes(x: &&i32) -> i32 {
    let mut c = x;
    let mut i = 0;
    while i < 3 {
        c = x;
        i += 1;
    }
    **c
}

fn main() {}
