use prusti_contracts::*;


#[ensures(result == 6)] //~ ERROR postcondition might not hold
fn func() -> u32{
    5
}

fn main() {

}
