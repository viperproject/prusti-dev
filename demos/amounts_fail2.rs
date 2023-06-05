use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

#[trusted]
#[ensures(alloced(1, loc))]
fn alloc(loc: usize) {
    // do allocation here
}

#[ensures(alloced(n + 1, loc))]
fn multialloc(loc: usize, n: usize) {
    let mut i = 0;
    while i < n {
        body_invariant!(alloced(i + 1, loc)); // error here: loop invariant might not hold in first
                                              // iteration
        alloc(loc);
        i += 1;
    }
}

#[ensures(alloced(13, 42))]
fn main() {
    multialloc(42, 13)
}

// with CHECK_OVERFLOWS=false

// DOES NOT VERIFY
