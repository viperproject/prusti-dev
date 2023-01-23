// extern crate prusti_contracts;
use prusti_contracts::*;

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

#[extern_spec]
mod std {
    mod mem {
        //extern crate prusti_contracts;
        use prusti_contracts::*;

        #[ensures(snap(dest) === src)]
        #[ensures(result === old(snap(dest)))]
        fn replace<T>(dest: &mut T, src: T) -> T;
    }
}

impl List {
    #[pure]
    #[requires(index < self.len())]
    pub fn lookup(&self, index: usize) -> i32 {
        self.head.lookup(index)
    }

    #[ensures(self.len() == old(self.len()) + 1)]
    #[ensures(self.lookup(0) == elem)]
    #[ensures(forall(|i: usize| (1 <= i && i < self.len()) ==>
                 old(self.lookup(i - 1)) == self.lookup(i)))] 
    pub fn push(&mut self, elem: i32) {
        let new_node = Box::new(Node {
            elem: elem,
            next: std::mem::replace(&mut self.head, Link::Empty),
        });

        self.head = Link::More(new_node);
    }

    #[pure]
    pub fn len(&self) -> usize {
        self.head.len()
    }

    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        List {
            head: Link::Empty,
        }
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