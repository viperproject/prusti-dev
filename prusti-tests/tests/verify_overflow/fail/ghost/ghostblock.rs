// compile-flags: -Punsafe_core_proof=true

#![allow(unused)]

use prusti_contracts::*;

fn empty_ghost_block() {
    ghost! {}
}

fn return_disallowed() {
    ghost! {
        return; //~ ERROR: Can't leave the ghost block early
    }
}

fn break_disallowed() {
    while true {
        ghost! {
            break; //~ ERROR: Can't leave the ghost block early
        }
    }
}

fn continue_disallowed(x: bool) {
    while true {
        ghost! {
            if x {
                continue; //~ ERROR: Can't leave the ghost block early
            } else {
                continue; //~ ERROR: Can't leave the ghost block early
            }
        }
    }
}

fn inner_loop_breaks_allowed() {
    ghost! {
        while true {
            break;
            continue;
        }
    }
}

fn inner_labeled_loop_allowed() {
    ghost! {
        'inner: while true {
            break;
        }
    }
}

fn cannot_break_outer_labeled_loop() {
    'outer: while true {
        ghost! {
            while true {
                continue 'outer; //~ ERROR: Can't leave the ghost block early
                break;
            }
        }
    }
}

fn main() {}
