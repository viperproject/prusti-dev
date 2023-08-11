use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

#[trusted]
#[ensures(alloced(1, loc))]
fn alloc(loc: usize) {}

fn main() { //~ ERROR function might leak instances of obligation `alloced`
    alloc(64);
}
