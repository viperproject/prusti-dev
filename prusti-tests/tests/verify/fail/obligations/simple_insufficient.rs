use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

#[ensures(alloced(1, 64))] //~ ERROR function might not produce resources asserted
fn main() {}
