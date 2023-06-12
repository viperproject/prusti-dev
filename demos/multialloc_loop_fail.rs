use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

#[trusted]
#[ensures(alloced(1, loc))]
fn alloc(loc: usize) {
}

#[ensures(forall(|i: usize| loc_from <= i && i < loc_to ==> alloced(1, i)))]
fn multialloc(loc_from: usize, loc_to: usize) {
    let mut loc = loc_from;
    while loc < loc_to {
        body_invariant!(forall(|i: usize| loc_from <= i && i < loc ==> alloced(1, i)));
        alloc(loc);
        loc += 1;
    }
}

#[ensures(alloced(1, 1))]
#[ensures(alloced(1, 2))]
#[ensures(alloced(1, 3))]
fn main() {
    multialloc(1, 5); // << should be (1, 4) here
    // error here: leak check might fail
}

// with CHECK_OVERFLOWS=false

// DOES NOT VERIFY
