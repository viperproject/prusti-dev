use prusti_contracts::*;

fn main() {}


fn third(s: &[i32]) -> i32 {
    s[2]  //~ ERROR the array or slice index may be out of bounds
}
