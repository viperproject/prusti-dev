use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

#[trusted]
#[ensures(alloced(1, loc))]
fn alloc(loc: usize) {}

#[trusted]
#[requires(alloced(1, loc))]
fn dealloc(loc: usize) {}

fn main() {
    alloc(1);
    alloc(2);
    alloc(3);

    dealloc(1);
    dealloc(3);
    dealloc(2);
}
