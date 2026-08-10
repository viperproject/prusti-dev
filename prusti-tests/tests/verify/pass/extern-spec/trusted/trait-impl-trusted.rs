//! An impl of an `extern_spec` trait can opt out of verification by marking
//! itself `#[trusted]`: its body is assumed rather than verified, so it passes
//! even though it violates the inherited contract. The (assumed) contract is
//! still used at call sites.

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

#[refine_trait_spec]
impl Hasher for H {
    #[trusted]
    fn finish(&self) -> u64 {
        self.v // violates `result == 0`, but is trusted
    }
    fn write(&mut self, _b: &[u8]) {}
}

fn main() {
    let h = H { v: 7 };
    let f = h.finish();
    prusti_assert!(f == 0); // assumed from the contract, not the (trusted) body
}
