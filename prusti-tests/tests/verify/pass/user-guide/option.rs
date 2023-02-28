//// ANCHOR: nothing
//// ANCHOR_END: nothing
// The next line is only required for doctests, you can ignore/remove it
extern crate prusti_contracts;
use prusti_contracts::*;

fn main() {}

pub struct List {
    head: Link,
}

type Link = Option<Box<Node>>;

struct Node {
    elem: i32,
    next: Link,
}

//// ANCHOR: option_take_extern_spec
#[extern_spec(std::mem)]
#[ensures(snap(dest) === src)]
#[ensures(result === old(snap(dest)))]
fn replace<T>(dest: &mut T, src: T) -> T;

//// ANCHOR_END: option_take_extern_spec
// Specs for std::option::Option<T>::unwrap(self) (and others) can be found here (work in progress):
// https://github.com/viperproject/prusti-dev/pull/1249/files#diff-bccda07f8a48357687e26408251041072c7470c188092fb58439de39974bdab5R47-R49

//// ANCHOR: option_take_extern_spec
#[extern_spec]
impl<T> std::option::Option<T> {
    //// ANCHOR_END: option_take_extern_spec
    #[requires(self.is_some())]
    #[ensures(old(self) === Some(result))]
    pub fn unwrap(self) -> T;
    
    #[pure]
    #[ensures(result == matches!(self, None))]
    pub const fn is_none(&self) -> bool;

    #[pure]
    #[ensures(result == matches!(self, Some(_)))]
    pub const fn is_some(&self) -> bool;

    //// ANCHOR: option_take_extern_spec
    #[ensures(result === old(snap(self)))]
    #[ensures(self.is_none())]
    pub fn take(&mut self) -> Option<T>;
}
//// ANCHOR_END: option_take_extern_spec

//// ANCHOR: try_pop_rewrite
//// ANCHOR: rewrite_link_impl
impl List {
    //// ANCHOR_END: try_pop_rewrite
    #[pure]
    pub fn len(&self) -> usize {
        link_len(&self.head)
    }

    //// ANCHOR_END: rewrite_link_impl
    #[pure]
    fn is_empty(&self) -> bool {
        matches!(self.head, None)
    }

    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        List { head: None }
    }

    //// ANCHOR: rewrite_link_impl
    #[pure]
    #[requires(index < self.len())]
    pub fn lookup(&self, index: usize) -> i32 {
        link_lookup(&self.head, index)
    }
    //// ANCHOR_END: rewrite_link_impl

    #[ensures(self.len() == old(self.len()) + 1)]
    #[ensures(self.lookup(0) == elem)]
    #[ensures(forall(|i: usize| (i < old(self.len())) ==>
                 old(self.lookup(i)) == self.lookup(i + 1)))]
    pub fn push(&mut self, elem: i32) {
        let new_node = Box::new(Node {
            elem,
            next: self.head.take(),
        });

        self.head = Some(new_node);
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
    //// ANCHOR: try_pop_rewrite
    pub fn try_pop(&mut self) -> Option<i32> {
        match self.head.take() { // Replace mem::swap with the buildin Option::take
            None => None,
            Some(node) => {
                self.head = node.next;
                Some(node.elem)
            }
        }
    }
    
    // // This will likely work in the future, but doesn't currently (even if you provide an `extern_spec` for `Option::map`):
    // // Currently you get this error:
    // //     [Prusti: unsupported feature] unsupported creation of unique borrows (implicitly created in closure bindings)
    // pub fn try_pop(&mut self) -> Option<i32> {
    //     let tmp = self.head.take();
    //     tmp.map(move |node| {
    //         self.head = node.next;
    //         node.elem
    //     })
    // }
    //// ANCHOR_END: try_pop_rewrite

    #[requires(!self.is_empty())]
    #[ensures(self.head_removed(&old(snap(self))))]
    #[ensures(result === old(snap(self)).lookup(0))]
    pub fn pop(&mut self) -> i32 {
        self.try_pop().unwrap()
        //// ANCHOR: rewrite_len
    }
    //// ANCHOR: rewrite_link_impl
    //// ANCHOR: try_pop_rewrite
}
//// ANCHOR_END: try_pop_rewrite
//// ANCHOR_END: rewrite_link_impl
//// ANCHOR_END: rewrite_len

//// ANCHOR: rewrite_link_impl
#[pure]
#[requires(index < link_len(link))]
fn link_lookup(link: &Link, index: usize) -> i32 {
    match link {
        Some(node) => {
            if index == 0 {
                node.elem
            } else {
                link_lookup(&node.next, index - 1)
            }
        }
        None => unreachable!(),
    }
}

#[pure]
fn link_len(link: &Link) -> usize {
    match link {
        None => 0,
        Some(node) => 1 + link_len(&node.next),
    }
}
//// ANCHOR_END: rewrite_link_impl

mod prusti_tests {
    use super::*;

    fn test_1(){
        let mut list = List::new(); // create an new, empty list
        prusti_assert!(list.is_empty() && list.len() == 0); // list should be empty

        list.push(5);
        prusti_assert!(!list.is_empty() && list.len() == 1); // the list should have a length of 1
        prusti_assert!(list.lookup(0) == 5); // the head of the list should be 5

        list.push(10);
        prusti_assert!(!list.is_empty() && list.len() == 2); // length correct
        prusti_assert!(list.lookup(0) == 10); // head is 10
        prusti_assert!(list.lookup(1) == 5); // 5 got pushed back correctly

        let x = list.pop();
        prusti_assert!(!list.is_empty() && list.len() == 1); // length correct
        prusti_assert!(list.lookup(0) == 5); // 5 should be at the head again
        prusti_assert!(x == 10); // pop returns the value that was added last

        if let Some(y) = list.try_pop() {
            prusti_assert!(list.is_empty() && list.len() == 0); // length correct
            prusti_assert!(y == 5); // correct value inside the `Some`
        } else {
            unreachable!() // This should not happen, since `try_pop` never returns `None`
        }

        let z = list.try_pop();
        prusti_assert!(list.is_empty() && list.len() == 0); // length correct
        prusti_assert!(z.is_none()); // trying to pop from an empty list should return `None`
    }

    #[requires(list_0.len() >= 4)]
    #[requires(!list_1.is_empty())]
    #[requires(list_0.lookup(1) == 42)]
    #[requires(list_0.lookup(3) == list_1.lookup(0))]
    fn test_2(list_0: &mut List, list_1: &mut List) {
        let x0 = list_0.pop();

        list_0.push(10);
        prusti_assert!(list_0.len() >= 4);
        prusti_assert!(list_0.lookup(1) == 42);
        prusti_assert!(list_0.lookup(1) == old(snap(list_0)).lookup(1));
        prusti_assert!(list_0.lookup(2) == old(snap(list_0)).lookup(2));
        prusti_assert!(list_0.lookup(3) == old(snap(list_0)).lookup(3));
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
}