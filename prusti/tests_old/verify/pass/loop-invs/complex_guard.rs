extern crate prusti_contracts;

fn test() {
    let mut i = 0;

    #[invariant="i == 0"]
    'outer: loop {
        #[invariant="i % 10 == 0 && i < 55"]
        while {
            let old_i = i;
            #[invariant="i < old_i + 10"]
            while i < old_i + 10 {
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
            i += 1;
            if i == 456456 {
                break;
            }
            if i == 567567 {
                continue;
            }
            i -= 1;
        }

        if i > 55 {
            break 'outer;
        } else {
            unreachable!();
        }
    }

    assert!(i == 60);
}

fn main() {}
