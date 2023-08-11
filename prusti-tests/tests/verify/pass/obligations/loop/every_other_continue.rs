use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

#[trusted]
#[ensures(alloced(1, loc))]
fn alloc(loc: usize) {}

#[trusted]
#[requires(alloced(1, loc))]
fn dealloc(loc: usize) {}

#[ensures(alloced(steps / 2, loc))]
fn every_other_alloc(loc: usize, steps: usize) {
    let mut i = 0;
    while i < steps {
        body_invariant!(alloced(i / 2, loc));
        if i % 2 == 0 {
            i += 1;
            continue;
        }
        alloc(loc);
        i += 1;
    }
}

fn main() {}
