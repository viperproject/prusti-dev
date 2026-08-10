//! Every function that gets a spec inside an `#[extern_spec]` must be marked
//! `#[trusted]`: its spec is always assumed, never verified, and the
//! annotation makes this explicit.

use prusti_contracts::*;

#[extern_spec]
impl i32 {
    #[pure]
    #[ensures(result >= 0)]
    fn abs(self) -> i32; //~ ERROR: must be marked `#[trusted]`
}

fn main() {}
