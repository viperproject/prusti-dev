use prusti_contracts::*;

fn main() {}


#[pure]
fn pure_oob(s: &[i32]) -> i32 {
    s[0]  //~ ERROR the array or slice index may be out of bounds
}

fn third(s: &[i32]) -> i32 {
    s[2]  //~ ERROR the array or slice index may be out of bounds
}
