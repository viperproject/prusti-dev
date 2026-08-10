//! The `#[trusted]` requirement also applies to a function that is listed in an
//! `#[extern_spec]` without any specification: it is either explicitly assumed,
//! or it does not need to be listed at all.

use prusti_contracts::*;

#[extern_spec]
impl i32 {
    fn abs(self) -> i32; //~ ERROR: must be marked `#[trusted]`
}

fn main() {}
