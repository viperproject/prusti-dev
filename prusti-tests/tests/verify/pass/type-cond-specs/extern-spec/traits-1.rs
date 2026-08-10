use prusti_contracts::*;
use core::hash::Hasher;

trait HasContract {
    #[pure]
    fn pre(&self) -> bool;
    #[pure]
    fn post(&self) -> bool;
}

struct S {
    x: i32,
}

// Type-conditional refinement attached to a foreign trait method.
#[extern_spec]
trait Hasher {
    #[trusted]
    #[refine_spec(where Self: HasContract, [
        requires(self.pre()),
        ensures(self.post())
    ])]
    fn write(&mut self, bytes: &[u8]);
}

impl Hasher for S {
    // Implicitly inherits the refined contract from the external specification
    // of `Hasher` (when `Self: HasContract`).
    fn write(&mut self, _bytes: &[u8]) {
        self.x += 10;
    }
    fn finish(&self) -> u64 {
        0
    }
}

#[refine_trait_spec]
impl HasContract for S {
    #[pure]
    fn post(&self) -> bool {
        self.x >= 20
    }
    #[pure]
    fn pre(&self) -> bool {
        self.x >= 10
    }
}

fn main() {
    let mut s = S { x: 10 };
    s.write(&[]);
    assert!(s.x >= 20);
}
