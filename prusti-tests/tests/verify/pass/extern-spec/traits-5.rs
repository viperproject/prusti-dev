extern crate prusti_contracts;
use prusti_contracts::*;

use std::clone::Clone;

struct PrustiStructstdcloneClone12e4123();

impl PrustiStructstdcloneClone12e4123 {
    #[prusti::extern_spec]
    #[requires(true)]
    fn clone(&self) -> Self {
        Clone::clone(&self);
        unimplemented!()
    }
}

fn main() {}