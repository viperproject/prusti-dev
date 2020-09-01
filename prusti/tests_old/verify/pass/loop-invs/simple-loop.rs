extern crate prusti_contracts;

fn test1(n: u32) -> u32 {
    let mut i = 0;
    while i < n {
        i += 1;
    }
    i
}

fn main() {}
