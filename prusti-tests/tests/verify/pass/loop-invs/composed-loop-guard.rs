use prusti_contracts::*;

fn test() {
    let mut i = 0;
    while i < 10 || true {
        i += 1;
    }
}

fn main() {}
