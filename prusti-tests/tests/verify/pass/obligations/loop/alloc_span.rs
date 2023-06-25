use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

#[trusted]
#[ensures(alloced(1, loc))]
fn alloc(loc: usize) {}

#[ensures(forall(|j: usize| { loc_from <= j && j < loc_to ==> alloced(1, j)}))]
fn alloc_span(loc_from: usize, loc_to: usize) {
    let mut i = loc_from;
    while i < loc_to {
        body_invariant!(loc_from <= i && forall(|j: usize| { loc_from <= j && j < i ==> alloced(1, j) }));
        alloc(i);
        i += 1;
    }
}

fn main() {}

