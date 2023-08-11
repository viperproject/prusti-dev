use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize);
}

#[trusted]
#[ensures(result ==> alloced(1))]
fn fast_alloc() -> bool {
    true
}

#[trusted]
#[ensures(alloced(1))]
fn slow_alloc() {}

#[ensures(alloced(1))]
fn mixed_alloc(tries: usize) {
    let mut i = 0;
    let mut done = false;
    while i < tries {
        if fast_alloc() {
            done = true;
            break;
        }
        i += 1;
    }
    if !done {
        slow_alloc();
    }
}

fn main() {}
