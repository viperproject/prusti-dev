//// ANCHOR: nothing
//// ANCHOR_END: nothing
use prusti_contracts::*;

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
//// ANCHOR: peek_mut_code
impl<T> List<T> {
    //// ANCHOR_END: peek_mut_code
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
    // pub fn try_peek(&mut self) -> Option<&T> {
    //     todo!()
    // }

    #[pure]
    #[requires(!self.is_empty())]
    pub fn peek(&self) -> &T {
        self.lookup(0)
    }
    
    // #[requires(index < self.len())]
    // pub fn lookup_mut(&mut self, index: usize) -> &mut T {
    //     let mut curr_node = &mut self.head;
    //     let mut index = index; // Workaround for Prusti not supporting mutable fn arguments
    //     while index != 0 {
    //         body_invariant!(true);
    //         if let Some(next_node) = curr_node { // reference in enum
    //             curr_node = &mut next_node.next;
    //         } else {
    //             unreachable!();
    //         }
    //         index -= 1;
    //     }
    //     if let Some(node) = curr_node { // ERROR: [Prusti: unsupported feature] the creation of loans in this loop is not supported (ReborrowingDagHasNoMagicWands)
    //         &mut node.elem
    //     } else {
    //         unreachable!()
    //     }
    // }

    //// ANCHOR: peek_mut_code
    #[trusted] // required due to unsupported reference in enum
    #[requires(!self.is_empty())]
    #[ensures(snap(result) === old(snap(self.peek())))]
    pub fn peek_mut(&mut self) -> &mut T {
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
    }
}
//// ANCHOR_END: peek_mut_code

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

//// ANCHOR: test_peek_mut
mod prusti_tests {
    use super::*;
    //// ANCHOR_END: test_peek_mut

    fn _test_1(){
        let mut list = List::new(); 
        prusti_assert!(list.is_empty() && list.len() == 0);

        list.push(5);
        prusti_assert!(!list.is_empty() && list.len() == 1);
        prusti_assert!(*list.lookup(0) == 5); // Here we can dereference the lookup, since `i32` is `Copy`

        list.push(10);
        prusti_assert!(!list.is_empty() && list.len() == 2); // length correct
        prusti_assert!(*list.lookup(0) == 10); // head is 10
        prusti_assert!(*list.lookup(1) == 5); // 5 got pushed back correctly

        let x = list.pop();
        prusti_assert!(!list.is_empty() && list.len() == 1); // length correct
        prusti_assert!(*list.lookup(0) == 5); // 5 should be at the head again
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
    #[requires(*list_0.lookup(1) == 42)]
    #[requires(list_0.lookup(3) == list_1.lookup(0))]
    fn _test_2(list_0: &mut List<i32>, list_1: &mut List<i32>) {
        let x0 = list_0.pop();

        list_0.push(10);
        prusti_assert!(list_0.len() >= 4);
        prusti_assert!(*list_0.lookup(1) == 42);
        prusti_assert!(list_0.lookup(1) == old(snap(list_0)).lookup(1));
        prusti_assert!(list_0.lookup(2) == old(snap(list_0)).lookup(2));
        prusti_assert!(list_0.lookup(3) == old(snap(list_0)).lookup(3));
        assert!(list_0.pop() == 10); // This cannot be a `prusti_assert`, since `pop` changes the list

        let x1 = list_0.pop();
        let x2 = list_0.pop();
        let x3 = list_0.pop();
        prusti_assert!(x0 == old(snap(list_0.lookup(0))));
        prusti_assert!(x1 == old(snap(list_0.lookup(1))) && x1 == 42);
        prusti_assert!(x2 == old(snap(list_0.lookup(2))));
        prusti_assert!(x3 == old(snap(list_0.lookup(3))));
        
        let y0 = list_1.pop();
        prusti_assert!(y0 == old(snap(list_1.lookup(0))));
        prusti_assert!(y0 == x3);
    }

    fn _test_3() {
        let mut list = List::new();
        list.push(16);
        prusti_assert!(list.peek() === list.lookup(0));
        prusti_assert!(*list.peek() == 16);
        
        list.push(5);
        prusti_assert!(list.peek() === list.lookup(0));
        prusti_assert!(*list.peek() == 5);

        list.pop();
        prusti_assert!(list.peek() === list.lookup(0));
        prusti_assert!(*list.peek() == 16);
    }

    //// ANCHOR: test_peek_mut
    fn _test_4() {
        let mut list = List::new();
        list.push(8);
        list.push(16);
        prusti_assert!(*list.lookup(0) == 16);
        prusti_assert!(*list.lookup(1) == 8);
        prusti_assert!(list.len() == 2);

        {
            let first = list.peek_mut();
            // `first` is a mutable reference to the first element of the list
            // for as long as `first` is live, `list` cannot be accessed
            prusti_assert!(*first == 16);
            *first = 5;
            prusti_assert!(*first == 5);
            // `first` gets dropped here, `list` can be accessed again
        }
        prusti_assert!(list.len() == 2); // Fails
        prusti_assert!(*list.lookup(0) == 5); // Fails
        prusti_assert!(*list.lookup(1) == 8); // Fails
    }
}
//// ANCHOR_END: test_peek_mut