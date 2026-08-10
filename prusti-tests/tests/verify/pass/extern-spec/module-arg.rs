//! Exercises the `#[extern_spec(path)]` module-path argument against real
//! `core`/`std` items (traits, free functions, module blocks and impls).

use prusti_contracts::*;
use core::hash::Hasher;

// Trait, addressed by a `core` module path.
#[extern_spec(core::hash)]
trait Hasher {
    #[trusted]
    #[ensures(result == 0)]
    fn finish(&self) -> u64;
}

// Free function, addressed by a `core` module path.
#[extern_spec(core::mem)]
#[trusted]
#[ensures(result == 4)]
fn size_of<T>() -> usize;

// Free function inside a module block, addressed by the enclosing path.
#[extern_spec(core)]
mod mem {
    #[trusted]
    #[ensures(result >= 1)]
    fn align_of<T>() -> usize;
}

// Method on a foreign type.
#[extern_spec]
impl i32 {
    #[trusted]
    #[pure]
    #[ensures(result >= 0)]
    fn abs(self) -> i32;
}

struct H {
    v: u64,
}

impl Hasher for H {
    fn finish(&self) -> u64 {
        0
    }
    fn write(&mut self, _b: &[u8]) {}
}

fn main() {
    let h = H { v: 9 };
    assert!(h.finish() == 0);
    assert!(core::mem::size_of::<i32>() == 4);
    assert!(core::mem::align_of::<i32>() >= 1);
    assert!((-4i32).abs() >= 0);
}
