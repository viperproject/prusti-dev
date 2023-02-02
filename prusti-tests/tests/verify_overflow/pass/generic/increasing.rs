use prusti_contracts::*;

#[extern_spec]
impl PartialOrd<i32> for i32{
    #[pure]
    #[ensures(result == (*self < *other))]
    fn lt(&self, other: &i32) -> bool;
}

predicate! {
    fn increasing<T: PartialOrd>(s: &[T]) -> bool {
        forall(|i: usize, j: usize|
            (i < j && j < s.len() ==> s[i] < s[j]))
    }
}

fn test() {
    let x = [1, 2, 3];
    prusti_assert!(increasing(&x));
}

fn main() {}
