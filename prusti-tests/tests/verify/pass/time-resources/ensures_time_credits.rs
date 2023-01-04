// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

#[requires(time_credits(bound + 1))]
#[ensures(time_receipts(result.0 + 1))]
#[ensures(time_credits(bound - result.0))]
fn bounded_sum(a: &[usize], bound: usize) -> (usize, usize) {
    let mut i = 0;
    let mut sum = 0;
    while i < a.len() && i < bound {
        body_invariant!(time_receipts(i + 1));
        sum += a[i];
        i += 1;
    }
    (i, sum)
}

enum LinkedList<T> {
    Empty,
    Cons(T, Box<LinkedList<T>>),
}

impl<T> LinkedList<T> {
    #[requires(time_credits(bound + 1))]
    #[ensures(time_receipts(result))]
    #[ensures(time_credits(bound - result))]
    fn bounded_len(&self, bound: usize) -> usize {
        if bound == 0 {
            0
        } else {
            match self {
                LinkedList::Empty => 0,
                LinkedList::Cons(_, tail) => tail.bounded_len(bound - 1) + 1,
            }
        }
    }
}

#[requires(time_credits(1))]
fn main() {}
