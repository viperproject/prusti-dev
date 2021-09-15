use prusti_contracts::*;

#[ensures(result == old(x))]
fn identity(x: i32) -> i32 {
    x
}

fn main() {

}
