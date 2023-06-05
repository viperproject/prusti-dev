use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

#[trusted]
#[ensures(alloced(1, loc))]
fn alloc(loc: usize) {
    // do allocation here
}

#[ensures(alloced(1, base + offset))]
fn alloc_offset(base: usize, offset: usize) {
    alloc(base + offset);
}

// << missing obligation in postcondition here
fn main() {
    alloc_offset(64, 3);
    // error here: leak check might not hold
}

// with CHECK_OVERFLOWS=false

// DOES NOT VERIFY
