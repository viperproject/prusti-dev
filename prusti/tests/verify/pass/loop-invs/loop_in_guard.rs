extern crate prusti_contracts;

fn test_loop_in_guard() {
    let mut i = 0;

    #[invariant="i % 10 == 0 && i < 60"]
    while {
        let old_i = i;
        #[invariant="i < old_i + 10"]
        while i < old_i + 10 {
            i += 1;
        }
        i < 55
    } {
        continue
    }

    assert!(i == 60);
}

fn main() {}
