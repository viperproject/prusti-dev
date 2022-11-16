use prusti_contracts::*;

fn test_break() {
    let mut i = 0;
    'label: while {
        if i == 10 { break 'label; }
        false
    } {
        body_invariant!(true);
        continue
    }
    assert!(i == 10); //~ ERROR might not hold
}

fn test_continue() {
    let mut i = 0;
    'label: while { //~ ERROR loop invariant cannot be in a conditional branch
        if i < 10 {
            i += 1;
            continue 'label;
        }
        false
    } {
        body_invariant!(true);
        continue
    }
    assert!(i == 10);
}

fn main() {}
