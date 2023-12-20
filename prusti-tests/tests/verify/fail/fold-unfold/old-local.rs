extern crate prusti_contracts;
use prusti_contracts::*;

fn blah(y: i32){
    let x = 1;
    prusti_assert!(old(x) == 1); //~ ERROR old expressions should not contain local variables
}

fn main(){
}
