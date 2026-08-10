//! `extern_spec` for a concrete foreign function (a non-trait inherent method):
//! its spec is assumed (the target's body is never verified) and used at call
//! sites. The `#[trusted]` annotation is mandatory to make this explicit.

use prusti_contracts::*;

#[extern_spec]
impl i32 {
    #[trusted]
    #[pure]
    #[ensures(result >= 0)]
    fn abs(self) -> i32;
}

fn main() {
    let a = (-3i32).abs();
    assert!(a >= 0); // holds via the assumed extern-spec
}
