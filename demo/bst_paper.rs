#![allow(dead_code)]

use prusti_contracts::*; 
use std::cmp::{Ord, Ordering::{self, Equal, Less, Greater}};







//#[invariant(self.bst_invariant())]
pub enum Tree<T: Ord> {
    Node(T, Box<Tree<T>>, Box<Tree<T>>),
    Empty,
}

use Tree::{Node,Empty};


impl<T: Ord> Tree<T> {
    #[pure]
    pub fn contains(&self, find_value: &T) -> bool {
        match self {
            Node(value, left, right) =>
                match find_value.cmp(value) {
                    Equal   => true,
                    Less    => left.contains(find_value),
                    Greater => right.contains(find_value)
                },
            Empty => false
        }
    }

    
//    #[ensures(self.contains(&new_value))]
//    #[ensures(forall(|i: &T| matches!(i.cmp(&new_value), Less | Greater) 
//                             ==> self.contains(i) == old(self.contains(i))))]
pub fn insert(&mut self, new_value: T) {
    match self {
        Node(value, left, right) => 
            match new_value.cmp(value) {
                Equal => (),
                Less => left.insert(new_value),
                Greater => right.insert(new_value),
            },
        Empty => 
            *self = Tree::Node(new_value, Box::new(Empty), Box::new(Empty))
    }
}

    /*#[assert_on_expiry(
        // Must hold before result can expire
        match old(self) {
          Node(_,left,right) => 
               forall(|i: &T| left.contains(i) ==> 
                                             matches!(i.cmp(result), Less))
            && forall(|i: &T| right.contains(i) ==> 
                                             matches!(i.cmp(result), Greater)),
          Empty => false
        },
        // A future guarantee of `get_root_value` after result expires
        self.contains(before_expiry(result)) &&
        forall(|i: &T| matches!(i.cmp(before_expiry(result)), Less | Greater) 
          ==> 
            (self.contains(i) ==> old(self.contains(i))))
    )]*/

    
    //#[requires(matches!(self, Node(..)))]
    
    // only call on non-empty trees!
    pub fn get_root_value(&mut self) -> &mut T {
        match self {
            Node(value, _, _) => value,
            Empty => unreachable!()
        }
    }
    

/*
    predicate! {
        pub fn bst_invariant(&self) -> bool {
            match self {
                Empty => true,
                Node(value, left, right) =>
                    forall(|i: &T| left.contains(i) == 
                        (self.contains(i) && matches!(i.cmp(value), Less))) 
                    &&
                    forall(|i: &T| right.contains(i) == 
                        (self.contains(i) && matches!(i.cmp(value), Greater)))
            }
        }
    }
*/








}























#[extern_spec]
trait Ord {
    #[pure]
    #[ensures(match (result, other.cmp(self)) {
        (Equal, Equal) |
        (Less, Greater) |
        (Greater, Less) => true,
        _ => false,
    })]
    #[ensures(forall(|x: &Self| match (result, other.cmp(x), self.cmp(x)) {
        (Equal, Equal, Equal) => true,
        (Equal, Less, Less) => true,
        (Equal, Greater, Greater) => true,
        (Less, Equal, Less) => true,
        (Less, Less, Less) => true,
        (Less, Greater, _) => true,
        (Greater, Equal, Greater) => true,
        (Greater, Less, _) => true,
        (Greater, Greater, Greater) => true,
        _ => false,
    }))]
    fn cmp(&self, other: &Self) -> Ordering;
}





















/*
#[extern_spec]
impl Ord for i32 {
    #[pure]
    #[ensures(matches!(result, Equal) == (*self == *other))]
    #[ensures(matches!(result, Less) == (*self < *other))]
    #[ensures(matches!(result, Greater) == (*self > *other))]
    fn cmp(&self, other: &Self) -> Ordering;
}
*/

fn main() {
    /*let mut t = Tree::Empty;
    t.insert(0);
    if let Tree::Node(value, left, right) = &t {
        assert!(matches!(**left, Tree::Empty));
        assert!(matches!(**right, Tree::Empty));
        assert!(*value == 0);
    } else {
        unreachable!()
    }*/
}