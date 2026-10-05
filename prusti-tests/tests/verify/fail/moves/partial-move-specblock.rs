use prusti_contracts::*;

pub fn basic_partial_move() {
    let x = (String::new(), 5);
    let _y = x.0;
    prusti_assert!(x.1 == 6); //~ ERROR: assertion might not hold
}

#[requires(x.1 == 5)]
pub fn box_partial_move(x: Box<(String, i32)>) {
    let _y = x.0;
    prusti_assert!(x.1 == 6); //~ ERROR: assertion might not hold
}
