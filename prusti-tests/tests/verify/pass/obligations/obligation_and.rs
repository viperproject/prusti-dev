use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

obligation! {
    fn outstanding(amount: usize, loc: usize);
}

#[trusted]
#[requires(alloced(1, loc))]
fn dealloc(loc: usize) {}

#[trusted]
#[requires(outstanding(1, loc))]
fn send(loc: usize) {}

#[requires(alloced(1, loc) & outstanding(1, loc))]
fn process(loc: usize) {
    send(loc);
    dealloc(loc);
}

fn main() {}
