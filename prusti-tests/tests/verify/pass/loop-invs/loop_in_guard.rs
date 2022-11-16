use prusti_contracts::*;

fn test_loop_in_guard() {
    let mut i = 0;

    while {
        body_invariant!(i % 10 == 0 && i < 60);
        let old_i = i;
        while i < old_i + 10 {
            body_invariant!(i < old_i + 10);
            i += 1;
        }
        i < 55
    } {
        continue
    }

    assert!(i == 60);
}

fn main() {}
