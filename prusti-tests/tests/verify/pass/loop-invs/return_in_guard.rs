use prusti_contracts::*;

fn test() {
    let mut i = 0;

    while {
        if i < 10 {
            return;
        }
        i < 55
    } {
        i += 1;
        assert!(false); // Unreachable
    }

    assert!(i == 55);
}

fn main() {}
