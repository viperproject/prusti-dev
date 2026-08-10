//! The impl STRENGTHENS the precondition of an `extern_spec` trait method:
//! rejected by behavioral subtyping (an impl pre must be implied by the
//! trait's).

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
    #[requires(i >= 3)] //~ ERROR: the implementation's precondition may be stronger than the trait method's
    fn write_u32(&mut self, i: u32) {
        self.v = i as u64;
    }
    fn finish(&self) -> u64 {
        0
    }
    fn write(&mut self, _b: &[u8]) {}
}

fn main() {}
