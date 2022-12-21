// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

enum LinkedList<T> {
    Empty,
    Cons(T, Box<LinkedList<T>>),
}

impl<T> LinkedList<T> {
    #[requires(time_credits(1))]
    #[ensures(time_receipts(1))]
    #[ensures(result.pure_len() == 0)]
    fn new_empty() -> Self {
        LinkedList::Empty
    }

    #[requires(time_credits(1))]
    #[ensures(time_receipts(1))]
    #[ensures(result.pure_len() == self.pure_len() + 1)]
    fn cons(self, head: T) -> Self {
        LinkedList::Cons(head, Box::new(self))
    }

    #[pure]
    fn pure_len(&self) -> usize {
        match self {
            LinkedList::Empty => 0,
            LinkedList::Cons(_, tail) => tail.pure_len() + 1,
        }
    }

    #[requires(time_credits(self.pure_len() + 1))]
    #[ensures(time_receipts(result + 1))]
    #[ensures(self.pure_len() == result)]
    fn len(&self) -> usize {
        match self {
            LinkedList::Empty => 0,
            LinkedList::Cons(_, tail) => tail.len() + 1,
        }
    }
}

#[requires(time_credits(7))]
#[ensures(time_receipts(7))]
fn main() {
    let list = LinkedList::new_empty();
    let list1 = list.cons(1);
    let list2 = list1.cons(2);
    let len = list2.len();
    assert!(len == 2);
}
