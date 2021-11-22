use prusti_contracts::*;

#[pure]
fn convert(x: [u32; 2]) -> (u32, u32) {
    (x[0], x[1])
}

fn main() {
    let a = [123, 456];
    let b = (123, 123);
    assert!(convert(a) == b); //~ ERROR the asserted expression might not hold
}
