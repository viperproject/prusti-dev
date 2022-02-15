use prusti_contracts::*;

#[assert_on_expiry(*result == 42, true)]
fn must_answer(location: &mut i32) -> &mut i32 {
    location
}

fn test() {
    let mut x = 0;
    let y = must_answer(&mut x); //~ ERROR obligation might not hold on borrow expiry
    //*y = 42;
}

fn main() {}
