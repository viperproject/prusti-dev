use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

fn main() {
    let mut i = 1;
    loop {
        body_invariant!(alloced(i, 0)); //~ ERROR there might be not enough resources for the loop invariant to hold in the first loop iteration
        i += 1;
    }
}
