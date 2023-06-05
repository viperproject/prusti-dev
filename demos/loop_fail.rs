use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

#[trusted]
#[requires(alloced(1, loc))]
fn dealloc(loc: usize) {
    // do deallocation here
}

#[requires(alloced(4, loc))]
fn dealloc_more(loc: usize) {
    let mut i = 0;
    while i < 10 {
        body_invariant!(alloced(2, loc)); // << error here: insufficient permissions for invariant
                                          // after iteration
        dealloc(loc);
        i += 1;
    }
    dealloc(loc);
    dealloc(loc);
    dealloc(loc);
}
// ^^^ this would probably verify if obligations were implemented naively without scope_id

fn main() {
}

// with CHECK_OVERFLOWS=false

// DOES NOT VERIFY
