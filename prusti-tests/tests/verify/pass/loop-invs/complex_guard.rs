use prusti_contracts::*;

fn test() {
    let mut i = 0;

    'outer: loop {
        body_invariant!(i == 0);
        while {
            let old_i = i;
            while i < old_i + 10 {
                body_invariant!(i < old_i + 10);
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
            body_invariant!(i % 10 == 0 && i < 55);
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
