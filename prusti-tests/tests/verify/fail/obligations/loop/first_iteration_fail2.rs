use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

#[trusted]
#[ensures(alloced(1, loc))]
fn alloc(loc: usize) {}

#[ensures(alloced(n + 1, loc))]
fn multialloc(loc: usize, n: usize) {
    let mut i = 0;
    while i < n {
        body_invariant!(alloced(i + 1, loc)); //~ ERROR there might be not enough resources for the loop invariant to hold in the first loop iteration
        alloc(loc);
        i += 1;
    }
}

fn main() {}
