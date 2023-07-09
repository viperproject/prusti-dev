use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

#[ensures(alloced(1, loc))]
fn alloc(loc: usize) {
    prusti_inhale!(alloced(1, loc));
}

#[requires(alloced(1, loc))]
fn dealloc(loc: usize) {
    prusti_exhale!(alloced(1, loc));
}

fn main() {
    prusti_inhale!(alloced(1, 42));
    alloc(42);
    prusti_exhale!(alloced(2, 42));
}
