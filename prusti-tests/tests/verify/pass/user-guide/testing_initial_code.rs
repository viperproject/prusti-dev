// The next line is only required for doctests, you can ignore/remove it
extern crate prusti_contracts;
use prusti_contracts::*;

fn main() {}

pub struct List {
    head: Link,
}

enum Link {
    Empty,
    More(Box<Node>),
}

struct Node {
    elem: i32,
    next: Link,
}

#[extern_spec(std::mem)]
#[ensures(snap(dest) === src)]
#[ensures(result === old(snap(dest)))]
fn replace<T>(dest: &mut T, src: T) -> T;

// Specs for std::option::Option<T>::unwrap(self) (and others) can be found here (work in progress):
// https://github.com/viperproject/prusti-dev/pull/1249/files#diff-bccda07f8a48357687e26408251041072c7470c188092fb58439de39974bdab5R47-R49

#[extern_spec]
impl<T> std::option::Option<T> {
    #[requires(self.is_some())]
    #[ensures(old(self) === Some(result))]
    pub fn unwrap(self) -> T;
    
    #[pure]
    #[ensures(result == matches!(self, None))]
    pub const fn is_none(&self) -> bool;

    #[pure]
    #[ensures(result == matches!(self, Some(_)))]
    pub const fn is_some(&self) -> bool;
}

impl List {
    #[pure]
    pub fn len(&self) -> usize {
        self.head.len()
    }

    #[pure]
    fn is_empty(&self) -> bool {
        self.head.is_empty()
    }

    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        List { head: Link::Empty }
    }

    #[pure]
    #[requires(index < self.len())]
    pub fn lookup(&self, index: usize) -> i32 {
        self.head.lookup(index)
    }

    #[ensures(self.len() == old(self.len()) + 1)]
    #[ensures(self.lookup(0) == elem)]
    #[ensures(forall(|i: usize| (i < old(self.len())) ==>
                 old(self.lookup(i)) == self.lookup(i + 1)))]
    pub fn push(&mut self, elem: i32) {
        let new_node = Box::new(Node {
            elem,
            next: std::mem::replace(&mut self.head, Link::Empty),
        });

        self.head = Link::More(new_node);
    }

    predicate! {
        // two-state predicate to check if the head of a list was correctly removed
        fn head_removed(&self, prev: &Self) -> bool {
            self.len() == prev.len() - 1 // The length will decrease by 1
            && forall(|i: usize| // Every element will be shifted forwards by one
                (1 <= i && i < prev.len())
                    ==> prev.lookup(i) == self.lookup(i - 1))
        }
    }

    #[ensures(old(self.is_empty()) ==>
        result.is_none() &&
        self.is_empty()
    )]
    #[ensures(!old(self.is_empty()) ==>
        self.head_removed(&old(snap(self)))
        &&
        result === Some(old(snap(self)).lookup(0))
    )]
    pub fn try_pop(&mut self) -> Option<i32> {
        match std::mem::replace(&mut self.head, Link::Empty) {
            Link::Empty => None,
            Link::More(node) => {
                self.head = node.next;
                Some(node.elem)
            }
        }
    }

    #[requires(!self.is_empty())]
    #[ensures(self.head_removed(&old(snap(self))))]
    #[ensures(result === old(snap(self)).lookup(0))]
    pub fn pop(&mut self) -> i32 {
        self.try_pop().unwrap()
    }
}

impl Link {
    #[pure]
    #[requires(index < self.len())]
    pub fn lookup(&self, index: usize) -> i32 {
        match self {
            Link::More(node) => {
                if index == 0 {
                    node.elem
                } else {
                    node.next.lookup(index - 1)
                }
            }
            Link::Empty => unreachable!(),
        }
    }

    #[pure]
    fn len(&self) -> usize {
        match self {
            Link::Empty => 0,
            Link::More(node) => 1 + node.next.len(),
        }
    }

    #[pure]
    fn is_empty(&self) -> bool {
        matches!(self, Link::Empty)
    }
}

//// ANCHOR: test_1
//// ANCHOR: test_2
#[cfg(prusti)]
mod prusti_tests {
    use super::*;

    //// ANCHOR_END: test_2
    fn _test_list(){
        let mut list = List::new(); // create an new, empty list
        prusti_assert!(list.is_empty() && list.len() == 0); // list should be empty

        list.push(5);
        list.push(10);
        prusti_assert!(!list.is_empty() && list.len() == 2); // length correct
        prusti_assert!(list.lookup(0) == 10); // head is 10
        prusti_assert!(list.lookup(1) == 5); // 5 got pushed back correctly

        let x = list.pop();
        prusti_assert!(x == 10); // pop returns the value that was added last

        match list.try_pop() {
            Some(y) => assert!(y == 5),
            None => unreachable!()
        }

        let z = list.try_pop();
        prusti_assert!(list.is_empty() && list.len() == 0); // length correct
        prusti_assert!(z.is_none()); // `try_pop` on an empty list should return `None`
    }
    //// ANCHOR_END: test_1

    //// ANCHOR: test_2
    // This shows a test that takes 2 lists as input parameters:
    #[requires(list_0.len() >= 4)]
    #[requires(!list_1.is_empty())]
    #[requires(list_0.lookup(1) == 42)]
    #[requires(list_0.lookup(3) == list_1.lookup(0))]
    fn _test_lists(list_0: &mut List, list_1: &mut List) {
        let x0 = list_0.pop();

        list_0.push(10);
        prusti_assert!(list_0.len() >= 4);
        prusti_assert!(list_0.lookup(1) == 42);
        assert!(list_0.pop() == 10); // Cannot be `prusti_assert`, `pop` changes the list

        let x1 = list_0.pop();
        let x2 = list_0.pop();
        let x3 = list_0.pop();
        prusti_assert!(x0 == old(snap(list_0)).lookup(0));
        prusti_assert!(x1 == old(snap(list_0)).lookup(1) && x1 == 42);
        prusti_assert!(x2 == old(snap(list_0)).lookup(2));
        prusti_assert!(x3 == old(snap(list_0)).lookup(3));
        
        let y0 = list_1.pop();
        prusti_assert!(y0 == old(snap(list_1)).lookup(0));
        prusti_assert!(y0 == x3);
    }
    //// ANCHOR: test_1
}
//// ANCHOR_END: test_1
//// ANCHOR_END: test_2