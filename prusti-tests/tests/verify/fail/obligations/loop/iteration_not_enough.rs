use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

fn main() {
    let mut i = 0;
    loop {
        body_invariant!(alloced(i, 0)); //~ ERROR there might be not enough resources for the loop invariant to hold after a loop iteration
        i += 1;
    }
}
