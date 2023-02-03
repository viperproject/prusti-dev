use prusti_contracts::*;

predicate! {
    fn foo(x: usize) -> usize {
        x + 1
    }
}

fn main() {
    prusti_assert!(foo(2) == 3);
}
