//! The impl WEAKENS the precondition of an `extern_spec` trait method (allowed:
//! the trait pre implies the impl pre). Call sites resolve to the impl's own
//! contract: the call below satisfies only the impl's weaker pre, so it
//! verifies iff the impl's pres (not the trait stub's) are used.

use prusti_contracts::*;
use core::hash::Hasher;

struct H {
    v: u64,
}

#[extern_spec]
trait Hasher {
    #[trusted]
    #[requires(i >= 2)]
    fn write_u32(&mut self, i: u32);
}

#[refine_trait_spec]
impl Hasher for H {
    #[requires(i >= 1)]
    fn write_u32(&mut self, i: u32) {
        self.v = i as u64;
    }
    fn finish(&self) -> u64 {
        0
    }
    fn write(&mut self, _b: &[u8]) {}
}

fn main() {
    let mut h = H { v: 0 };
    h.write_u32(1); // satisfies the impl's pre but not the trait's
}
