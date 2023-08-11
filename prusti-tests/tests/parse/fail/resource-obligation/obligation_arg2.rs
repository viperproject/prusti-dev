use prusti_contracts::*;

obligation! {
    fn obl(loc: usize, sector: i32); //~ ERROR the first argument of the function in `obligation!` must be `amount: usize`
}

fn main() {}
