use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

#[trusted]
#[ensures(alloced(1, loc))]
fn alloc(loc: usize) {}

#[ensures(alloced(amount, loc))]
fn repeat_alloc(loc: usize, amount: usize) {
    let mut i = 0;
    while i < amount {
        body_invariant!(alloced(i, loc));
        alloc(loc);
        i += 1;
    }
}

fn main() {}
