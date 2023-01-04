// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

enum LinkedList<T> {
    Empty,
    Cons(T, Box<LinkedList<T>>),
}

impl<T> LinkedList<T> {
    #[requires(time_credits(bound + 1))]
    #[ensures(time_receipts(result))]
    #[ensures(time_credits(bound - result + 1))]
    fn bounded_len(&self, bound: usize) -> usize { //~ ERROR Not enough time credits at the end of the function.
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
