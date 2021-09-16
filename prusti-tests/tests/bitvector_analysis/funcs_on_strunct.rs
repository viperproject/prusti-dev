extern crate prusti_contracts;
use prusti_contracts::*;

struct Pos {
    x:u8,
    y:u8
}


fn foo(p:Pos) -> Pos {   
    Pos {
        x: p.x & 0,
        y: p.y
    }
}

// fn bar(p:Pos) -> Pos {
//     Pos {
//         x: p.x + 1,
//         y: p.y
//     }
// }

fn main() {}