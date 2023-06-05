use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

#[trusted]
#[ensures(alloced(1, loc))]
fn alloc(loc: usize) {
    // do allocation here
}

#[ensures(alloced(n, loc))]
fn multialloc(loc: usize, n: usize) {
    let mut i = 0;
    while i < n + 1 { // << should be just n without the +1 here
        body_invariant!(alloced(i, loc));
        alloc(loc);
        i += 1;
    }
    // error here: leak check might fail
}

#[ensures(alloced(13, 42))]
fn main() {
    multialloc(42, 13)
}

// with CHECK_OVERFLOWS=false

// DOES NOT VERIFY
