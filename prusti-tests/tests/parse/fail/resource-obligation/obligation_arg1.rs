use prusti_contracts::*;

obligation! {
    fn obl(); //~ ERROR the first argument of the function in `obligation!` must be `amount: usize`
}

fn main() {}
