extern crate prusti_contracts;
use prusti_contracts::*;

#[pure]
fn get_third(v: &Vec<u32>) -> u32 {
    v[2] //~ ERROR Using usize as index/range type for &std::vec::Vec<u32> is not supported yet
}

fn main(){}
