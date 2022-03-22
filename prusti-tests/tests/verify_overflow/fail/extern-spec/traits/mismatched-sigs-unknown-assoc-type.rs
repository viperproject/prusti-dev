// ignore-test for now, associated types cannot be declared
// eventually (with specs on associated types), we will want this error

use prusti_contracts::*;

#[extern_spec]
trait Iterator {
    type Item;
    type Unknown; //~ ERROR: associated type `Unknown` not found for `std::iter::Iterator`

    fn next(&mut self) -> Option<Self::Item>;
}

fn main() {}
