use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

fn main() {
    prusti_assume!(alloced(1, 64));
    prusti_assert!(false);
}
