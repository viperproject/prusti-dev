use prusti_contracts::*;

obligation! {
    fn obl(loc: usize, sector: i32); //~ ERROR the first argument of an obligation
}

fn main() {}
