extern crate prusti_contracts;
use prusti_contracts::*;


#[pure]
fn main() {
    let mut i = 5; 

    while i > 0 {
        i = i - 1;
    }
}
