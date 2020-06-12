extern crate prusti_contracts;

fn test() {
    let mut i = 0;

    #[invariant="true"]
    'outer: loop {
        #[invariant="i < 55"]
        'inner: while {
            #[invariant="i % 10 != 0 && i < 60"]
            while i % 10 != 0 {
                if i == 123123 {
                    break;
                }
                if i == 234234 {
                    continue;
                }
                i += 1;
            }
            i < 55
        } {
            i -= 1;
            if i == 456456 {
                break;
            }
            if i == 567567 {
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
