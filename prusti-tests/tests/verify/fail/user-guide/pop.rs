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

//// ANCHOR: is_empty
//// ANCHOR: initial
//// ANCHOR: pop_precondition
impl List {
    //// ANCHOR_END: initial
    //// ANCHOR_END: is_empty
    //// ANCHOR_END: pop_precondition
    #[pure]
    pub fn len(&self) -> usize {
        self.head.len()
    }
    
    //// ANCHOR: is_empty
    #[pure]
    fn is_empty(&self) -> bool {
        self.head.is_empty()
    }
    //// ANCHOR_END: is_empty

    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        List {
            head: Link::Empty,
        }
    }

    #[pure]
    #[requires(index < self.len())]
    pub fn lookup(&self, index: usize) -> i32 {
        self.head.lookup(index)
    }

    #[ensures(self.len() == old(self.len()) + 1)] //~ ERROR postcondition might not hold
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

    //// ANCHOR: initial
    pub fn try_pop(&mut self) -> Option<i32> {
        match std::mem::replace(&mut self.head, Link::Empty) {
            Link::Empty => None,
            Link::More(node) => {
                self.head = node.next;
                Some(node.elem)
            },
        }
    }
    
    //// ANCHOR_END: initial
    //// ANCHOR: pop_precondition
    #[requires(!self.is_empty())]
    //// ANCHOR: initial
    pub fn pop(&mut self) -> i32 {
        self.try_pop().unwrap()
    }
    //// ANCHOR: is_empty
}
//// ANCHOR_END: is_empty
//// ANCHOR_END: initial
//// ANCHOR_END: pop_precondition

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
            },
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