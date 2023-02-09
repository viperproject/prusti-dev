use prusti_contracts::*;

predicate! {
    fn foo(x: i64) -> bool {
        let y = x + 1;
        y > x
    }
}

fn main() {}
