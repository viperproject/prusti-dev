extern crate prusti_contracts;

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
