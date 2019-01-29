extern crate prusti_contracts;

fn test(x: u32, y: u32) -> u32 {
    x + y //~ ERROR
}

fn main() {}
