use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

fn main() {
    prusti_assert!(alloced(1, 64)) //~ ERROR there might be not enough resources for the asserted expression to hold
}

fn another() {
    prusti_exhale!(alloced(1, 64)) //~ ERROR there might be not enough resources for the exhale
}
