extern crate prusti_contracts;

fn test(x: u64, y: u64) -> u64 {
    x / y //~ ERROR
}

fn main() {}
