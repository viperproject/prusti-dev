extern crate prusti_contracts;
use prusti_contracts::*;

/// External traits
trait MyTrait {
    fn foo(&self);
}
/// External traits

trait A {}
trait B {}
trait C {}

#[extern_spec]
trait MyTrait where Self: A + B, Self: C { //~ ERROR: Where clauses for extern traits specs are not supported
    fn foo(&self);
}

fn main() {}