extern crate prusti_contracts;

fn test() {
    let mut i = 0;

    while {
        while i % 10 != 0 {
            i += 1;
        }
        assert!(i % 10 == 0);
        i < 55
    } {
        i -= 1;
    }

    assert!(i == 60);
}

fn main() {}
