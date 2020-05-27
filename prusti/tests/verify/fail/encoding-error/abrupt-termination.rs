extern crate prusti_contracts;

fn test_continue() {
    let mut i = 0;
    while i < 10 {
        if i == 5 {
            i += 2;
            continue; // OK
        }
        i += 1;
    }
}

fn test_break() {
    let mut i = 0;
    while i < 10 {
        if i == 5 { //~ ERROR not supported
            i += 1;
            i += 10;
            i += 1000;
            break;
        }
        i += 1;
    }
}

fn test_return() {
    let mut i = 0;
    while i < 10 {
        if i == 5 { //~ ERROR not supported
            i += 1;
            i += 10;
            i += 1000;
            return;
        }
        i += 1;
    }
}

fn test_unreachable_break() {
    let mut i = 0;
    #[invariant="i <= 10"]
    while i < 10 {
        if i == 50 {
            i += 1;
            i += 10;
            i += 1000;
            break; // OK
        }
        i += 1;
    }
}

fn test_unreachable_return() {
    let mut i = 0;
    #[invariant="i <= 10"]
    while i < 10 {
        if i == 50 {
            i += 1;
            i += 10;
            i += 1000;
            return; // OK
        }
        i += 1;
    }
}

fn main() {}
