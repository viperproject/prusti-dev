use prusti_contracts::*;

fn test1() {
    let mut i = 0;
    while i < 10 {
        body_invariant!(i < 10);
        i += 1;
    }
    assert!(i == 10);
}

#[ensures(result == (old(*i) >= 0))]
#[ensures(*i == 1 + old(*i))]
fn test_and_increment(i: &mut usize) -> bool {
    let old_i = *i;
    *i += 1;
    old_i >= 0
}

#[requires(*i > 0)]
fn work(i: &mut usize) {
    // ...
}

fn client() {
    let mut i = 0;
    while test_and_increment(&mut i) {
        body_invariant!(i > 0);
        work(&mut i);
    }
    assert!(i <= 0);
}

fn main() {}
