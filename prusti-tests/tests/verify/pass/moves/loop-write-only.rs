use prusti_contracts::*;

pub struct W {
    v: i32,
}

// `c` holds a value on loop entry and is only overwritten in the loop: the
// invariant keeps its value, which the first write drops.
pub fn plain_reassign_in_loop() {
    let mut c = 0;
    let mut i = 0;
    while i < 3 {
        body_invariant!(0 <= i && i <= 3);
        c = i;
        i += 1;
    }
    prusti_refute!(false);
}

pub fn struct_reassign_in_loop() {
    let mut c = W { v: 0 };
    let mut i = 0;
    while i < 3 {
        body_invariant!(0 <= i && i <= 3);
        c = W { v: i };
        i += 1;
    }
    prusti_refute!(false);
}

// The invariant at the PCG loop head itself.
pub fn no_body_invariant() {
    let mut c = 0;
    let mut i = 0;
    while i < 3 {
        c = i;
        i += 1;
    }
    prusti_refute!(false);
}

pub fn invariant_at_loop_head() {
    let mut c = 0;
    let mut i = 0;
    loop {
        body_invariant!(0 <= i && i <= 3);
        if i >= 3 {
            break;
        }
        c = i;
        i += 1;
    }
    prusti_refute!(false);
}

pub fn read_after_loop() {
    let mut c = 0;
    let mut i = 0;
    while i < 3 {
        body_invariant!(0 <= i && i < 3 && (i == 0 || c == i - 1));
        c = i;
        i += 1;
    }
    assert!(c == 2);
}

pub fn struct_read_after_loop() {
    let mut c = W { v: 0 };
    let mut i = 0;
    while i < 3 {
        body_invariant!(0 <= i && i < 3 && c.v == i - 1 || i == 0);
        c = W { v: i };
        i += 1;
    }
    assert!(c.v == 2);
}
