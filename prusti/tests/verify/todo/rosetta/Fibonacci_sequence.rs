/// An adaptation of the example from
/// https://rosettacode.org/wiki/Fibonacci_sequence#Rust

extern crate prusti_contracts;

use std::mem;

#[pure]
fn fib(i: usize) -> usize {
    match i {
        0 => 0,
        1 => 1,
        n => fib(n-1) + fib(n-2),
    }
}

#[trusted]
#[requires="fib(i) == n"]
fn print_fib(i: usize, n: usize) {
    println!("{}", n);
}

#[trusted]
#[ensures="*a == old(*b)"]
#[ensures="*b == old(*a)"]
fn swap(a: &mut usize, b: &mut usize) {
    mem::swap(a, b);
}

#[trusted]
#[ensures="result.is_some() ==> a + b == result.peek()"]
fn checked_add(a: usize, b: usize) -> UsizeOption {
    match a.checked_add(b) {
        Some(n) => UsizeOption::Some(n),
        None => UsizeOption::None,
    }
}

enum UsizeOption {
    Some(usize),
    None,
}

impl UsizeOption {
    #[pure]
    fn is_some(&self) -> bool {
        match self {
            UsizeOption::Some(_) => true,
            UsizeOption::None => false,
        }
    }
    #[requires="self.is_some()"]
    #[ensures="result == old(self.peek())"]
    fn unwrap(self) -> usize {
        match self {
            UsizeOption::Some(n) => n,
            UsizeOption::None => unreachable!(),
        }
    }
    #[pure]
    #[requires="self.is_some()"]
    fn peek(&self) -> usize {
        match self {
            UsizeOption::Some(n) => *n,
            UsizeOption::None => unreachable!(),
        }
    }
}

/*
fn iterative_fibonacci() {
    let mut prev = 0;
    // Rust needs this type hint for the checked_add method
    let mut curr = 1usize;

    while let Some(n) = curr.checked_add(prev) {
        prev = curr;
        curr = n;
        println!("{}", n);
    }
}

fn fibonacci(mut prev: usize, mut curr: usize) {
    mem::swap(&mut prev, &mut curr);
    if let Some(n) = curr.checked_add(prev) {
        println!("{}", n);
        fibonacci(prev, n);
    }
}
*/

struct Fib {
    prev: usize,
    curr: usize,
    _ghost_counter: usize,
}

impl Fib {
    #[ensures="result.valid()"]
    #[ensures="result.counter() == 1"]
    fn new() -> Self {
        Fib {prev: 0, curr: 1, _ghost_counter: 1}
    }
    #[pure]
    fn counter(&self) -> usize {
        self._ghost_counter
    }
    #[pure]
    fn valid(&self) -> bool {
        self._ghost_counter >= 1 &&
        self.prev == fib(self._ghost_counter-1) &&
        self.curr == fib(self._ghost_counter)
    }
    #[requires="self.valid()"]
    #[ensures="result.is_some() ==> self.valid()"]
    #[ensures="result.is_some() ==> fib(self.counter()) == result.peek()"]
    fn next(&mut self) -> UsizeOption {
        swap(&mut self.curr, &mut self.prev);
        if let UsizeOption::Some(n) = checked_add(self.curr, self.prev) {
            self.curr = n;
            self._ghost_counter += 1;
            UsizeOption::Some(n)
        }
        else {
            UsizeOption::None
        }
    }
}

fn main() {
    let mut iter = Fib::new();
    let mut continue_iteration = true;
    #[invariant="continue_iteration ==> iter.valid()"]
    while continue_iteration {
        let item = iter.next();
        if item.is_some() {
            let i = iter.counter();
            let n = item.unwrap();
            print_fib(i, n);
        } else {
            continue_iteration = false;
        }
    }
}
