use prusti_contracts::*;

struct Point {
    x: i32,
    y: i32,
}

#[ensures(*result == pt.x)]
fn get_mut_x<'a, 'b: 'a>(pt: &'b Point) -> &'a i32 {
    &pt.x
}

fn main() {}
