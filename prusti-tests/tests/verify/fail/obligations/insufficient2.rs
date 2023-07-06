use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

#[trusted]
#[ensures(alloced(1, loc))]
fn alloc(loc: usize) {}

#[ensures(alloced(1, base) & alloced(1, base + offset))] //~ ERROR function might not produce resources
fn alloc_offset(base: usize, offset: usize) {
    alloc(base);
}

#[ensures(alloced(1, 64) & alloced(1, 67))]
fn main() {
    alloc_offset(64, 3)
}
