extern crate prusti_contracts;

fn test(x: isize, y: isize) -> isize {
    x / y //~ ERROR overflow
}

fn main() {}
