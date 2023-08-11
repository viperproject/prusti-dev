use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

#[trusted]
#[ensures(alloced(1, loc))]
fn alloc(loc: usize) {}

#[requires(alloced(1, 42))]
#[requires(alloced(2, 42))]
#[requires(alloced(3, 42))]
#[ensures(alloced(7, 42))]
fn main() {
    alloc(42);
}
