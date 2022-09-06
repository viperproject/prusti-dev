use prusti_contracts::*;

trait Trait {
    type Assoc: Copy;

    #[pure] fn output_copy(&self) -> Self::Assoc;
    #[pure] fn input_copy(&self, x: Self::Assoc) -> bool;
}

#[requires(x.output_copy() === y)]
#[requires(x.input_copy(z))]
fn test<U: Copy, T: Trait<Assoc = U>>(x: &mut T, y: U, z: U) {}

#[trusted]
fn main() {}
