use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

#[trusted]
#[ensures(alloced(1, loc))]
fn alloc(loc: usize) {
    // do allocation here
}

#[trusted]
#[requires(alloced(1, loc))]
fn dealloc(loc: usize) {
    // do deallocation here
}

#[ensures(alloced(1, base + offset))]
fn alloc_offset(base: usize, offset: usize) {
    alloc(base + offset);
}

#[ensures(alloced(1, 67))]
fn main() {
    alloc_offset(32, 1);
    alloc_offset(64, 3);
    dealloc(33);
}

// with CHECK_OVERFLOWS=false

// VERIFIES
