//// ANCHOR: nothing
//// ANCHOR_END: nothing
// The next line is only required for doctests, you can ignore/remove it
extern crate prusti_contracts;
use prusti_contracts::*;

fn main() {}

pub struct List<T> {
    head: Link<T>,
}

type Link<T> = Option<Box<Node<T>>>;

struct Node<T> {
    elem: T,
    next: Link<T>,
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

    #[ensures(result === old(snap(self)))]
    #[ensures(self.is_none())]
    pub fn take(&mut self) -> Option<T>;
}
//// ANCHOR: pledge
impl<T> List<T> {
    //// ANCHOR_END: pledge
    #[pure]
    pub fn len(&self) -> usize {
        link_len(&self.head)
    }

    #[pure]
    fn is_empty(&self) -> bool {
        matches!(self.head, None)
    }

    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        List { head: None }
    }

    #[pure]
    #[requires(index < self.len())]
    pub fn lookup(&self, index: usize) -> &T {
        link_lookup(&self.head, index)
    }

    #[ensures(self.len() == old(self.len()) + 1)]
    #[ensures(snap(self.lookup(0)) === elem)]
    #[ensures(forall(|i: usize| (i < old(self.len())) ==>
                 old(self.lookup(i)) === self.lookup(i + 1)))]
    pub fn push(&mut self, elem: T) {
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
                    ==> prev.lookup(i) === self.lookup(i - 1))
        }
    }

    #[ensures(old(self.is_empty()) ==>
        result.is_none() &&
        self.is_empty()
    )]
    #[ensures(!old(self.is_empty()) ==>
        self.head_removed(&old(snap(self)))
        &&
        result === Some(snap(old(snap(self)).lookup(0)))
    )]
    pub fn try_pop(&mut self) -> Option<T> {
        match self.head.take() { // Replace mem::swap with the buildin Option::take
            None => None,
            Some(node) => {
                self.head = node.next;
                Some(node.elem)
            }
        }
    }

    #[requires(!self.is_empty())]
    #[ensures(self.head_removed(&old(snap(self))))]
    #[ensures(result === old(snap(self)).lookup(0))]
    pub fn pop(&mut self) -> T {
        self.try_pop().unwrap()
    }

    // // Not currently possible in Prusti
    // pub fn try_peek(&self) -> Option<&T> {
    //     todo!()
    // }

    #[pure]
    #[requires(!self.is_empty())]
    pub fn peek(&self) -> &T {
        self.lookup(0)
    }

    #[trusted] // required due to unsupported reference in enum
    #[requires(!self.is_empty())]
    #[ensures(snap(result) === old(snap(self.peek())))]
    //// ANCHOR: pledge
    #[after_expiry(
        old(self.len()) === self.len() // (1.)
        && forall(|i: usize| 1 <= i && i < self.len() // (2.)
            ==> old(snap(self.lookup(i))) === snap(self.lookup(i)))
        && snap(self.peek()) === before_expiry(snap(result)) // (3.)
    )]
    pub fn peek_mut(&mut self) -> &mut T {
        //// ANCHOR_END: pledge
        // This does not work in Prusti at the moment:
        // "&mut self.head" has type "&mut Option<T>"
        // this gets auto-dereferenced by Rust into type: "Option<&mut T>"
        // this then gets matched to "Some(node: &mut T)"
        // References in enums are not yet supported, so this cannot be verified by Prusti
        if let Some(node) = &mut self.head {
            &mut node.elem
        } else {
            unreachable!()
        }
        //// ANCHOR: pledge
        // ...
    }
}
//// ANCHOR_END: pledge

//// ANCHOR: assert_on_expiry
impl List<i32> {
    predicate!{
        fn is_valid(&self) -> bool {
            forall(|i: usize| i < self.len()
                ==> *self.lookup(i) >= 0 && *self.lookup(i) < 16)
        }
    }
    // ==> { let value = *self.lookup(i);
    //     0 <= value && value < 16 })

    #[trusted] // required due to unsupported reference in enum
    #[requires(!self.is_empty())]
    #[requires(self.is_valid())]
    #[ensures(snap(result) === old(snap(self.peek())))]
    #[assert_on_expiry(
        0 <= *result && *result < 16,
        self.is_valid()
        && old(self.len()) === self.len() // (1.)
        && forall(|i: usize| 1 <= i && i < self.len() // (2.)
            ==> old(snap(self.lookup(i))) === snap(self.lookup(i)))
        && snap(self.peek()) === before_expiry(snap(result)) // (3.)
    )]
    pub fn peek_mut_16(&mut self) -> &mut i32 {
        if let Some(node) = &mut self.head {
            &mut node.elem
        } else {
            unreachable!()
        }
    }
}
//// ANCHOR_END: assert_on_expiry

fn _test_assert_on_expiry() {
    let mut list = List::new();
    list.push(2);
    list.push(1);
    list.push(0);
    {
        let first = list.peek_mut_16();
        // *first = 16; // This gives an error: [Prusti: verification error] obligation might not hold on borrow expiry
        *first = 15;
    }
}

#[pure]
#[requires(index < link_len(link))]
fn link_lookup<T>(link: &Link<T>, index: usize) -> &T {
    match link {
        Some(node) => {
            if index == 0 {
                &node.elem
            } else {
                link_lookup(&node.next, index - 1)
            }
        }
        None => unreachable!(),
    }
}

#[pure]
fn link_len<T>(link: &Link<T>) -> usize {
    match link {
        None => 0,
        Some(node) => 1 + link_len(&node.next),
    }
}

#[cfg(prusti)]
mod prusti_tests {
    use super::*;

    fn _test_list(){
        let mut list = List::new(); // create an new, empty list
        prusti_assert!(list.is_empty() && list.len() == 0); // list should be empty

        list.push(5);
        list.push(10);
        prusti_assert!(!list.is_empty() && list.len() == 2); // length correct

        prusti_assert!(*list.lookup(0) == 10); // head is 10
        prusti_assert!(*list.lookup(1) == 5); // 5 got pushed back correctly

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

    fn _test_peek() {
        let mut list = List::new();
        list.push(16);
        prusti_assert!(list.peek() === list.lookup(0));
        prusti_assert!(*list.peek() == 16);
        
        list.push(5);
        prusti_assert!(*list.peek() == 5);

        list.pop();
        prusti_assert!(*list.peek() == 16);
    }

    fn _test_peek_mut() {
        let mut list = List::new();
        list.push(8);
        list.push(16);

        // Open a new scope using an opening bracket `{`
        // `first` will get dropped at the closing bracket `}`
        {
            let first = list.peek_mut();
            // `first` is a mutable reference to the first element of the list
            // for as long as `first` is exists, `list` cannot be accessed
            prusti_assert!(*first == 16);
            *first = 5; // Write 5 to the first slot of the list
            prusti_assert!(*first == 5);
            // `first` gets dropped here, `list` can be accessed again
        }
        prusti_assert!(list.len() == 2);
        prusti_assert!(*list.lookup(0) == 5); // slot 0 is now `5`
        prusti_assert!(*list.lookup(1) == 8); // slot 1 is unchanged
    }
}