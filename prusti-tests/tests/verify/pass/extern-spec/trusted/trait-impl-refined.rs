//! The impl provides its OWN (stronger) contract, refining an `extern_spec`
//! trait: the impl is verified against its own contract, which is also what
//! call sites get (the assert below is only provable from the impl's
//! `result == 0`, not the trait's `result <= 10`).

use prusti_contracts::*;
use core::hash::Hasher;

struct H {
    v: u64,
}

#[extern_spec]
trait Hasher {
    #[trusted]
    #[ensures(result <= 10)]
    fn finish(&self) -> u64;
}

#[refine_trait_spec]
impl Hasher for H {
    #[ensures(result == 0)]
    fn finish(&self) -> u64 {
        0
    }
    fn write(&mut self, _b: &[u8]) {}
}

fn main() {
    let h = H { v: 7 };
    let f = h.finish();
    assert!(f == 0);
}
