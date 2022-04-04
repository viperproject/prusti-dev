extern crate prusti_contracts;
use prusti_contracts::*;

fn main() {
    let a = Seq::single(0);
    let b = Seq::single(1);
    let _ = Seq::concat(a, b);
}
