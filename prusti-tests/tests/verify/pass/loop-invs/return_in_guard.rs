use prusti_contracts::*;

fn test() {
    let mut i = 0;

    while {
        body_invariant!(i == 0); // TODO: loop framing should guarantee this
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
