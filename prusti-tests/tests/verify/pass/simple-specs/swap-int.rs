use prusti_contracts::*;

#[ensures(*i == old(*j) && *j == old(*i))]
fn swap(i: &mut i32, j: &mut i32) {
    let tmp = *j;
    *j = *i;
    *i = tmp;
}

fn main() {
    let mut a = 5;
    let mut b = 10;
    swap(&mut a, &mut b);
}
