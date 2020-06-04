extern crate prusti_contracts;

// ignore-test Generation of errors for unsupported loop shapes is not ready yet

fn test() {
    let mut i = 0;
    while i < 10 || true {
        i += 1;
    }
}

fn main() {}
