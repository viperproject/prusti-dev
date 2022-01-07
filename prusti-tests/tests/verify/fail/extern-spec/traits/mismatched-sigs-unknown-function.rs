// ignore-test
extern crate prusti_contracts;
use prusti_contracts::*;

#[extern_spec]
trait Iterator {
    type Item;

    fn foo(&mut self); //~ ERROR: function or associated item not found
}

fn main() {

}