extern crate prusti_contracts;

fn main() {
    let mut i = 1000;

    #[invariant="i >= 2"]
    while i > 2 {
        i -= 1;
    }
}
