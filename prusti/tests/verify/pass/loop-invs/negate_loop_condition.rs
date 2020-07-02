extern crate prusti_contracts;

fn test_loop(b: bool) {
    let mut g = b;
    #[invariant="g"] // Ok, as the loop invariant is not reached after `g = false`
    while g {
        g = false;
    }
}

#[trusted]
fn main() {}
