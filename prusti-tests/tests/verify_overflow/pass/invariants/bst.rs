// compile-flags: -Penable_type_invariants=true
// ignore-test Invariant as stated is too weak to conclude that `contains` and
//   `contains_golden` have the same result.

use prusti_contracts::*;
fn main() {}

#[invariant(
    if let BST::Node { value, left, right } = &self {
        (if let Some(lb) = left.rightmost_value() {
            *value > lb
        } else { true })
        && (if let Some(ub) = right.leftmost_value() {
            *value < ub
        } else { true })
    } else { true }
)]
//Doesn't work, see below
// #[invariant(self.recursive_inv())]
enum BST {
    Node {
        value: i32,
        left: Box<BST>,
        right: Box<BST>,
    },
    Leaf,
}

impl BST {
    // [Issue 1]
    // Requires trusted, otherwise recursive call to itself in precondition (Prusti crash):
    // Not a solution since this hides the body (the main reason for making a fn pure)
    #[trusted]
    #[pure]
    fn leftmost_value(&self) -> Option<i32> {
        if let BST::Node { value, left, .. } = self {
            let lv = left.leftmost_value();
            if let Some(_) = lv { lv }
            else { Some(*value) }
        } else { None }
    }
    // Requires trusted, otherwise recursive call to itself in precondition (Prusti crash):
    // Not a solution since this hides the body (the main reason for making a fn pure)
    #[trusted]
    #[pure]
    fn rightmost_value(&self) -> Option<i32> {
        if let BST::Node { value, right, .. } = self {
            let rv = right.rightmost_value();
            if let Some(_) = rv { rv }
            else { Some(*value) }
        } else { None }
    }

    #[pure]
    #[ensures(result == self.contains_golden(val))]
    fn contains(&self, val: i32) -> bool {
        if let BST::Node { value, left, right } = self {
            if val == *value { true }
            else if val < *value {
                // [Issue 2]
                // Invariant should hold recursively (it doesn't with the old inv encoding):
                // [Prusti: verification error] precondition might not hold.
                left.contains(val)
            } else {
                right.contains(val)
            }
        } else { false }
    }
    #[pure]
    fn contains_golden(&self, val: i32) -> bool {
        if let BST::Node { value, left, right } = self {
            if val == *value { true }
            else {
                left.contains_golden(val) && right.contains_golden(val)
            }
        } else { false }
    }

    //Trying to manually resolve "Issue 2" runs into "Issue 1":
    //(It doesn't help since `trusted` hides the recursive `left.recursive_inv()`)
    // #[trusted]
    // #[pure]
    // fn recursive_inv(&self) -> bool {
    //     if let BST::Node { value, left, right } = &self {
    //         (if let Some(lb) = left.rightmost_value() {
    //             *value > lb
    //         } else { true })
    //         && (if let Some(ub) = right.leftmost_value() {
    //             *value < ub
    //         } else { true })
    //         && left.recursive_inv() && right.recursive_inv()
    //     } else { true }
    // }
}
