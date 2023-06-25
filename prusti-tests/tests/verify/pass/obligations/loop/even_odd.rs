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

#[ensures(steps % 2 == 1 ==> alloced(1, loc))]
fn repeat_alloc(loc: usize, steps: usize) {
    let mut i = 0;
    while i < steps {
        body_invariant!(i % 2 == 1 ==> alloced(1, loc));
        if i % 2 == 0 {
            alloc(loc);
        } else {
            dealloc(loc);
        }
        i += 1;
    }
}

fn main() {}
