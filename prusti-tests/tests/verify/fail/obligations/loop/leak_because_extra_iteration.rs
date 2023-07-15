use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

#[trusted]
#[ensures(alloced(1, loc))]
fn alloc(loc: usize) {}

#[ensures(alloced(n, loc))]
fn multialloc(loc: usize, n: usize) { //~ ERROR function might leak instances of obligation `alloced`
    let mut i = 0;
    while i < n + 1 {
        body_invariant!(alloced(i, loc));
        alloc(loc);
        i += 1;
    }
}

#[ensures(alloced(13, 42))]
fn main() {
    multialloc(42, 13)
}
