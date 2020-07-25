//! An adaptation of the example from
//! https://rosettacode.org/wiki/Fibonacci_sequence#Rust
//!
//!
//! Omitted:
//!
//! +   Analytical version:
//!
//!     +   Uses closures.
//!     +   Uses floating point numbers.
//!
//! Changes:
//!
//! +   Replaced ``println!`` with calling trusted functions.
//! +   Unified function types.
//! +   Renamed functions.
//! +   Added ghost counters to prove that all versions generate the same sequence.
//! +   Rewrote loops into supported shape (while bool with no break, continue, or return).
//! +   Rewrote closure into a match statement.
//! +   Replaced Iterator::next function with a function next.
//! +   Wrapped built-in types and functions.
//!
//! Verified properties:
//!
//! +   Absence of panics.
//! +   The verified three implementations print only Fibonacci numbers.

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
#[requires="fib(_i) == n"]
fn print_fib(_i: usize, n: usize) {
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

// Iterative

fn iterative_fibonacci() {
    let mut prev = 0;
    // Rust needs this type hint for the checked_add method
    let mut curr = 1usize;

    let mut _ghost_counter = 1;
    let mut add_succeeded = true;

    #[invariant="_ghost_counter >= 1"]
    #[invariant="fib(_ghost_counter) == curr"]
    #[invariant="fib(_ghost_counter-1) == prev"]
    while add_succeeded {
        if let UsizeOption::Some(n) = checked_add(curr, prev) {
            prev = curr;
            curr = n;
            _ghost_counter += 1;
            print_fib(_ghost_counter, curr);
        } else {
            add_succeeded = false;
        }
    }
}

// Recursive

#[requires="_ghost_counter >= 1"]
#[requires="fib(_ghost_counter-1) == prev"]
#[requires="fib(_ghost_counter) == curr"]
fn recursive_fibonacci(_ghost_counter: usize, prev: usize, curr: usize) {
    let mut prev = prev;
    let mut curr = curr;
    swap(&mut prev, &mut curr);
    if let UsizeOption::Some(n) = checked_add(curr, prev) {
        print_fib(_ghost_counter+1, n);
        recursive_fibonacci(_ghost_counter+1, prev, n);
    }
}

// Using an Iterator

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
    #[pure]
    #[requires="self.is_some()"]
    fn peek(&self) -> usize {
        match self {
            UsizeOption::Some(n) => *n,
            UsizeOption::None => unreachable!(),
        }
    }
}

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
    #[invariant="iter.valid()"]
    while continue_iteration {
        let item = iter.next();
        match item {
            UsizeOption::Some(n) => {
                let i = iter.counter();
                print_fib(i, n);
            }
            UsizeOption::None => {
                continue_iteration = false;
            }
        }
    }
    iterative_fibonacci();
    recursive_fibonacci(1, 0, 1);
}
