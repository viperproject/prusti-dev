use prusti_contracts::*;

fn main() {
    let mut x = Vec::new();
    x.push(1);
    x.push(2);
    x.push(3);
    x[0] = x[1] + x[2];
    prusti_assert!(x[0] == 5);
    prusti_assert!(x[1] == 2);
    prusti_assert!(x[2] == 3);
}
