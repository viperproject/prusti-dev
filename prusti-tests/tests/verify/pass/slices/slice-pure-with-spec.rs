use prusti_contracts::*;

fn main() {}


#[pure]
#[ensures(s.len() > 0 ==> result == s[0])]
#[ensures(s.len() == 0 ==> result == 42)]
fn slice_first(s: &[i32]) -> i32 {
    if s.len() == 0 {
        42
    } else {
        s[0]
    }
}
