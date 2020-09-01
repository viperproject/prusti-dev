/// An adaptation of the example from Nicholas D. Matsakis
/// [blog](http://smallcultfollowing.com/babysteps/blog/2018/06/15/mir-based-borrow-check-nll-status-update/)
/// that illustrates differences between Rust 2018 NLL and Polonius.
///
/// Changes:
///
/// +   Rewrote to remove a return statement.
/// +   Wrapped built-in types and functions.
///
/// Verified properties:
///
/// +   Absence of panics.
/// +   Absence of overflows.

extern crate prusti_contracts;

pub struct VecWrapper<T>{
    v: Vec<T>
}

impl<T> VecWrapper<T> {

    #[trusted]
    #[ensures="result.len() == 0"]
    pub fn new() -> Self {
        VecWrapper{ v: Vec::new() }
    }

    #[trusted]
    #[ensures="self.len() == old(self.len()) + 1"]
    pub fn push(&mut self, value: T) {
        self.v.push(value);
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
}

#[pure]
#[trusted]
fn some_condition<T>(r: &T) -> bool {
    unimplemented!();
}

#[trusted]
fn default<T>() -> T {
    unimplemented!();
}


#[requires="vec.len() > 0"]
pub fn foo<T>(vec: &mut VecWrapper<T>) -> &T {
    let r = vec.index(0);
    if some_condition(r) {
        r
    } else {
        vec.push(default());
        let last = vec.len()-1;
        vec.index(last)
    }
}

fn main() {}
