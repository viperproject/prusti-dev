use prusti_contracts::*;

pub enum E3 {
    V1(u32),
    V2(u32),
}

pub fn test3(e: &mut E3) -> &mut u32 {  //~ ERROR implicit type invariants might not hold at the end of the method.
    match e {
        E3::V1(ref mut b) => {
            *b -= 5;
            b
        },
        E3::V2(ref mut b) => b,
    }
}

fn main() {}
