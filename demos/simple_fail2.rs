use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

#[trusted]
#[ensures(alloced(1, loc))]
fn alloc(loc: usize) {
    // do allocation here
}

#[ensures(alloced(1, base + offset))] // error here: insufficient permissions for postcondition
fn alloc_offset(base: usize, offset: usize) {
    alloc(base); // << missing '+ offset' here
    // error here: leak check might not hold
}

#[ensures(alloced(1, 67))]
fn main() {
    alloc_offset(64, 3)
}

// with CHECK_OVERFLOWS=false

// DOES NOT VERIFY
