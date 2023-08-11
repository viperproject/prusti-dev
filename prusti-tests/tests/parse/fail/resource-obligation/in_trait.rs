use prusti_contracts::*;

trait TheTrait {
    resource! {
        fn reso(amount: usize, a: i32); //~ ERROR `resource!` declarations are not allowed inside traits
    }

    obligation! {
        fn obl(amount: usize); //~ ERROR `obligation!` declarations are not allowed inside traits
    }
}

fn main() {}
