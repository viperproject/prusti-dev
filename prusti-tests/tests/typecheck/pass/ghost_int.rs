use prusti_contracts::*;
use crate::ghost::GhostInt;

fn test4() {
    let a = GhostInt;
    let b = GhostInt;
    let c = a + b;
}   
fn main() {}
