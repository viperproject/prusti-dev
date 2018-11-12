/// An adaptation of the example from
/// https://rosettacode.org/wiki/Binary_search#Rust

extern crate prusti_contracts;

pub struct VecWrapperI32{
    v: Vec<i32>
}

impl VecWrapperI32 {
    // Encoded as body-less Viper function
    #[trusted]
    #[pure]
    #[ensures="result >= 0"]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    // Encoded as body-less Viper method
    #[trusted]
    #[ensures="result.len() == 0"]
    pub fn new() -> Self {
        VecWrapperI32{ v: Vec::new() }
    }

    // Encoded as body-less Viper function
    #[trusted]
    #[pure]
    #[requires="0 <= index && index < self.len()"]
    pub fn lookup(&self, index: usize) -> i32 {
        self.v[index]
    }

    #[trusted]
    #[requires="0 <= index && index < self.len()"]
    pub fn borrow(&mut self, index: usize) -> &mut i32 {
        self.v.get_mut(index).unwrap()
    }

    // Encoded as body-less Viper method
    #[trusted]
    #[requires="index < self.len()"]
    #[ensures="self.len() == old(self.len())"]
    #[ensures="self.lookup(index) == value"]
    #[ensures="forall i: usize :: (0 <= i && i < self.len() && i != index) ==>
                    self.lookup(i) == old(self.lookup(i))"]
    pub fn store(&mut self, index: usize, value: i32) {
        self.v[index] = value;
    }

    #[trusted]
    #[ensures="self.len() == old(self.len()) + 1"]
    #[ensures="self.lookup(old(self.len())) == value"]
    #[ensures="forall i: usize :: (0 <= i && i < old(self.len())) ==>
                    self.lookup(i) == old(self.lookup(i))"]
    pub fn push(&mut self, value: i32) {
        self.v.push(value);
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
    #[pure]
    #[requires="self.is_some()"]
    fn peek(&self) -> usize {
        match self {
            UsizeOption::Some(n) => *n,
            UsizeOption::None => unreachable!(),
        }
    }
}

pub enum Ordering {
    Less,
    Equal,
    Greater,
}

use self::Ordering::*;

// Adapted from https://doc.rust-lang.org/src/core/cmp.rs.html#962-966
fn cmp(a: &mut i32, b: &mut i32) -> Ordering {
    if *a == *b { Equal }
    else if *a < *b { Less }
    else { Greater }
}


fn binary_search(arr: &mut VecWrapperI32, elem: &mut i32) -> UsizeOption
{
    let mut size = arr.len();
    let mut base = 0;

    let mut result = UsizeOption::None;
    //let mut finished = size > 2;
 
    //while finished {
        //size /= 2;
        let mid = base + size;

        let mid_element = arr.borrow(mid);
        let x = mid_element;
        //let cmp_result = cmp(mid_element, elem);
        //base = match cmp_result {
            //Less    => mid,
            //Greater => base,
            //Equal   => {
                //result = UsizeOption::Some(mid);
                //0   // Just return anything because we are finished.
            //}
        //};
        //finished = size > 2 || result.is_some();
    //}
 
    result
}

fn main() {}
