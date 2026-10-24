use prusti_contracts::*;

fn write_through_mut_ref() {
    let mut i = 0;
    let mut x = 0;
    while i < 3 {
        body_invariant!(0 <= i && i < 3);
        let r = &mut x;
        *r += 1;
        i += 1;
    }
}

fn write_through_mut_ref_after_branch(b: bool) {
    let mut i = 0;
    let mut x = 0;
    while i < 3 {
        if b {
            i += 1;
        }
        body_invariant!(0 <= i && i <= 3);
        let r = &mut x;
        *r += 1;
        if i == 3 {
            break;
        }
        i += 1;
    }
}
