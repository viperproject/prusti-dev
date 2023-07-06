use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

#[trusted]
#[ensures(alloced(1, loc))]
fn alloc(loc: usize) {}

#[requires(alloced(1, loc))]
fn dealloc(loc: usize) {}

#[requires(alloced(2, 1))]
#[ensures(alloced(1, 1))]
fn main() {
    dealloc(1);
    dealloc(444);
    dealloc(1);
    dealloc(1);

    alloc(893 + 77);
}
