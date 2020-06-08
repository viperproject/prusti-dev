extern crate prusti_contracts;

// ignore-test TODO: compute the loop invariant permissions for the correct program point

fn test() {
    let mut i = 0;

    'outer: loop {
        #[invariant="i < 55"]
        'inner: while {
            #[invariant="i % 10 != 0 && i < 60"]
            while i % 10 != 0 {
                i += 1;
            }
            if i == 345345 {
                continue 'outer;
            }
            if i == 456456 {
                continue 'inner;
            }
            assert!(i % 10 == 0);
            i < 55
        } {
            i -= 1;
            if i == 567567 {
                break;
            }
            if i == 678678 {
                continue;
            }
        }
        if i > 55 {
            break 'outer;
        }
    }

    assert!(i == 60);
}

fn main() {}
