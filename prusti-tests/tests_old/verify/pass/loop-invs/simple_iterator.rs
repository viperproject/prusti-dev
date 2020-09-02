extern crate prusti_contracts;

// ignore-test Unsupported loop. We don't yet generate magic wands in loop invariants, which are
// required when a loan is created before, and expires after, the loop invariant.

struct Fibonacci {
    curr: u32,
    next: u32,
}

impl Fibonacci {
    fn new() -> Self {
        Fibonacci { curr: 1, next: 1 }
    }
}

impl Iterator for Fibonacci {
    type Item = u32;

    fn next(&mut self) -> Option<u32> {
        let new_next = self.curr + self.next;

        self.curr = self.next;
        self.next = new_next;

        Some(self.curr)
    }
}

fn main(){
    let fib = Fibonacci::new();
    for _ in fib { }
}
