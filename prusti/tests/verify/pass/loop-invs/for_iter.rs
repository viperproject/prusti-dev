extern crate prusti_contracts;

// ignore-test TODO: the program has an empty magic wand

fn test() {
    let mut sum = 0;
    for i in 0..128 {
        sum += i;
    }
}

fn main() {}
