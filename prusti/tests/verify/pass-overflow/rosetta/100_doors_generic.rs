//! An adaptation of the example from
//! https://rosettacode.org/wiki/100_doors#Rust
//!
//! Omitted:
//!
//! +   Declarative version:
//!
//!     +   Uses closures.
//!
//! +   Optimized version: 
//!
//!     +   Uses closures.
//!
//! Changes:
//!
//! +   Replaced ``println!`` with calling trusted functions.
//! +   Wrapped built-in types and functions.
//! +   Rewrote loops into supported shape (while bool with no break, continue, or return).
//! +   Moved constants into variables.
//!
//! Verified properties:
//!
//! +   Absence of panics.

extern crate prusti_contracts;

pub struct VecWrapper<T>{
    v: Vec<T>
}

impl<T: Clone> VecWrapper<T> {

    #[trusted]
    #[ensures="result.len() == size"]
    pub fn new(value: T, size: usize) -> Self {
        VecWrapper { v: vec![value; size] }
    }

    #[trusted]
    #[pure]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[requires="0 <= index && index < self.len()"]
    pub fn index(&self, index: usize) -> &T {
        &self.v[index]
    }

    #[trusted]
    #[requires="0 <= index && index < self.len()"]
    #[ensures="after_expiry(self.len() == old(self.len()))"]
    pub fn index_mut(&mut self, index: usize) -> &mut T {
        &mut self.v[index]
    }

}

#[trusted]
fn print_door_state(i: usize, is_open: bool) {
    println!("Door {} is {}.", i + 1, if is_open {"open"} else {"closed"});
}

fn doors1() {
    let mut door_open = VecWrapper::new(false, 100);
    let mut pass = 1;
    #[invariant="pass < 100"]
    #[invariant="1 <= pass"]
    #[invariant="door_open.len() == 100"]
    while pass < 100 {
        let mut door = pass;
        #[invariant="door <= 100"]
        #[invariant="1 <= door"]
        #[invariant="door_open.len() == 100"]
        while door <= 100 {
            let door_state = !door_open.index(door - 1);
            let new_door_state = door_open.index_mut(door - 1);
            *new_door_state = door_state;
            door += pass;
        }
        pass += 1;
    }
    let mut i = 0;
    let mut continue_loop = i < door_open.len();
    #[invariant="0 <= i"]
    #[invariant="i < door_open.len()"]
    while continue_loop {
        let is_open = *door_open.index(i);
        print_door_state(i, is_open);
        i += 1;
        continue_loop = i < door_open.len();
    }
}

#[trusted]
#[requires="exp == 2 ==> base * base < std::u32::MAX"]
#[ensures="exp == 2 ==> result == base * base"]
fn pow(base: u32, exp: u32) -> u32 {
    base.pow(exp)
}

#[trusted]
fn print_door_open(i: u32) {
    println!("Door {} is open", i);
}

fn doors4() {
    let mut i = 1u32;
    let exp = 2;
    #[invariant="i < 10u32"]
    while i < 10u32 {
        let door = pow(i, exp);
        print_door_open(door);
        i += 1;
    }
}

fn main() {}
