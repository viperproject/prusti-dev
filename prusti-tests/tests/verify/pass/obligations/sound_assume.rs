use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

fn blackbox() -> i32 {
    -12
}

fn main() {
    let mut amount = 0;
    if blackbox() > 0 {
        amount = 1;
    }
    prusti_inhale!(alloced(amount, 64));
    prusti_assume!(alloced(1, 64));
    prusti_exhale!(alloced(amount, 64));

    prusti_assert!(amount == 1);
    prusti_refute!(false);
}


fn another() {
    prusti_inhale!(alloced(12, 10));
    prusti_assume!(alloced(1, 10));
    prusti_exhale!(alloced(12, 10));

    prusti_refute!(false);
}
