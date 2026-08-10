//! `extern_spec` for a foreign trait: the (mandatory) `#[trusted]` applies only
//! to the external functions themselves and is NOT inherited by impls. A local
//! impl is VERIFIED against the inherited contract (a correct one passes), and
//! the contract holds at call sites.
//!
//! The trait (`core::hash::Hasher`) and the contract (`finish() == 0`) are
//! deliberately arbitrary -- this only exercises the trusted/verified behaviour.

use prusti_contracts::*;
use core::hash::Hasher;

struct H {
    v: u64,
}

#[extern_spec]
trait Hasher {
    #[trusted]
    #[ensures(result == 0)]
    fn finish(&self) -> u64;
}

impl Hasher for H {
    fn finish(&self) -> u64 {
        0 // satisfies `result == 0`
    }
    fn write(&mut self, _bytes: &[u8]) {}
}

fn main() {
    let h = H { v: 7 };
    let f = h.finish();
    assert!(f == 0); // holds via the verified, inherited contract
}
