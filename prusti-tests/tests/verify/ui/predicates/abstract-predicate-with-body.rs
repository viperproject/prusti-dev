use prusti_contracts::*;

trait MyTrait {
    predicate! {
        fn foo(&self) -> bool {
            true
        }
    }
}

fn main() {
}
