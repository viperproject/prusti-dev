use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

#[trusted]
#[requires(alloced(1, loc))]
fn dealloc(loc: usize) {}

#[trusted]
#[ensures(result ==> alloced(1, loc))]
fn try_alloc(loc: usize) -> bool {
    true
}

#[ensures(result ==> forall(|j: usize| { loc_from <= j && j < loc_to ==> alloced(1, j)}))]
fn try_alloc_span(loc_from: usize, loc_to: usize, steps: usize) -> bool {
    let mut i = loc_from;
    while i < loc_to {
        body_invariant!(loc_from <= i && forall(|j: usize| { loc_from <= j && j < i ==> alloced(1, j) }));
        if !try_alloc(i) {
            let mut i2 = i;
            while i2 > loc_from {
                body_invariant!(forall(|j: usize| { loc_from <= j && j < i2 ==> alloced(1, j) }));
                dealloc(i2 - 1);
                i2 -= 1;
            }
            return false;
        }
        i += 1;
    }
    true
}

fn main() {}
