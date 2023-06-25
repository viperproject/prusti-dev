use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize);
}

#[trusted]
#[ensures(result ==> alloced(1))]
fn try_alloc() -> bool {
    true
}

#[trusted]
#[requires(alloced(1))]
fn dealloc() {}

fn main() {
    if try_alloc() {
        dealloc();
    }
}

