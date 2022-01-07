extern crate prusti_contracts;
use prusti_contracts::*;

#[extern_spec]
trait Iterator {
    type Item;
    type Unknown; //~ ERROR: associated type `Unknown` not found for `std::iter::Iterator`

    fn next(&mut self) -> Option<Self::Item>;
}

fn main() {

}