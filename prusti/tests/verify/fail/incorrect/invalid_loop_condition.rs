extern crate prusti_contracts;

fn test_break() {
    let mut i = 0;
    #[invariant="true"]
    'label: while {
        if i == 10 { break 'label; } //~ ERROR not allowed
        false
    } {
        continue
    }
    assert!(i == 10);
}

fn test_continue() {
    let mut i = 0;
    #[invariant="true"]
    'label: while {
        if i < 10 { i += 1; continue 'label; } //~ ERROR loop invariant cannot be in a conditional branch
        false
    } {
        continue
    }
    assert!(i == 10);
}

fn main() {}
