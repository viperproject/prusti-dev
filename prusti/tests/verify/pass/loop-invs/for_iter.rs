extern crate prusti_contracts;

// ignore-test Unsupported loop. We don't yet generate magic wands in loop invariants, which are
// required when a loan is created before, and expires after, the loop invariant.

fn test1() {
    let mut sum = 0;
    for i in 0..128 {
        sum += i;
    }
}

fn test2() {
    let mut sum = 0;
    let mut generator = 0..128;
    for i in generator {
        sum += i;
    }
}

fn test3() {
    let mut sum = 0;
    let mut generator = 0..128;
    while let Some(i) = generator.next() {
        sum += i;
    }
}

fn main() {}
