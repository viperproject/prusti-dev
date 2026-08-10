//! The `#[trusted]` of an `extern_spec` trait method is NOT inherited by
//! impls: a local impl that violates the inherited contract is caught by
//! verification. To opt out it would have to be `#[trusted]` itself.

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
        self.v //~ ERROR: postcondition might not hold
    }
    fn write(&mut self, _bytes: &[u8]) {}
}

fn main() {}
