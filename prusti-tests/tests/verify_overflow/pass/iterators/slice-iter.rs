// compile-flags: -Penable_iterators=true
// compile-flags: -Penable_ghost_constraints=true

#![feature(associated_type_bounds)]
extern crate prusti_contracts;
use prusti_contracts::*;

use std::slice::Iter;
use std::cmp::PartialEq;
use std::iter::Iterator;

trait IteratorSpecExt {
    type IterItem: Copy;

    #[pure]
    #[trusted]
    fn visited(&self) -> GhostSeq<Self::IterItem> {
        unimplemented!()
    }

    predicate! {
        fn enumerated(&self) -> bool;
    }

    predicate! {
        fn two_state_postcondition(new_self: &Self, old_self: &Self) -> bool;
    }

    predicate! {
        fn completed(&self) -> bool;
    }
}

#[model]
struct Iter<'a, #[generic] T: Copy+PartialEq+Sized> {
    position: usize,
    data: GhostSeq<T>,
}

type SliceTy<T> = [T];
#[extern_spec]
impl<T: Copy+PartialEq> SliceTy<T> {
    #[pure]
    fn len(&self) -> usize;

    // Initialize the model
    #[requires(self.len() >= 0)]
    #[ensures( result.model().position == 0 )]
    #[ensures( result.model().data.len() == self.len() )]
    #[ensures(
    forall(|i: usize| 0 <= i && i < self.len() ==> (
    self[i] == result.model().data.lookup(i)
    ))
    )]
    // Initialize ghost sequence of visited values
    #[ensures(
    result.visited().len() == 0
    )]
    fn iter(&self) -> std::slice::Iter<'_, T>;
}

#[extern_spec]
trait Iterator {
    #[requires(false)]
    #[ghost_constraint(Self: IteratorSpecExt<IterItem = <Self as Iterator>::Item> , [
    requires(self.enumerated()),
    ensures(self.enumerated()),
    ensures(
    (!old(self.completed()) == result.is_some()) &&
    (old(self.completed()) == result.is_none()) &&
    (old(self.completed()) ==> self.completed())
    ),
    ensures(IteratorSpecExt::two_state_postcondition(old(self), self))
    ])]
    fn next(&mut self) -> Option<Self::Item>;
}

#[refine_trait_spec]
impl<'a, T: Copy + PartialEq + 'a> IteratorSpecExt for std::slice::Iter<'a, T> {
    type IterItem = &'a T;

    predicate! {
        fn enumerated(&self) -> bool {
            self.visited().len() <= self.model().data.len() &&
            self.visited().len() == self.model().position &&
            forall(|i: usize| (0 <= i && i < self.visited().len()) ==>
                self.model().data.lookup(i) == *self.visited().lookup(i)
            )
        }
    }

    predicate! {
        fn two_state_postcondition(old_self: &Self, new_self: &Self) -> bool {
            // Data does not change
            // TODO iterators: Using GhostSeq::equals here does not work
            // new_self.model().data.equals(&old_self.model().data) &&
            new_self.model().data.len() == old_self.model().data.len() &&
            forall(|i: usize| (0 <= i && i < new_self.model().data.len()) ==> (
                new_self.model().data.lookup(i) == old_self.model().data.lookup(i)
            )) &&

            // How does the position evolve
            !old_self.completed() == (new_self.model().position == old_self.model().position + 1) &&
            old_self.completed() == (new_self.model().position == old_self.model().position)
        }
    }

    predicate! {
        fn completed(&self) -> bool {
            self.model().position >= self.model().data.len()
        }
    }
}

#[requires(iter.model().position == pos)]
#[requires(iter.model().data.len() == data_len)]
#[requires(iter.visited().len() == vis_len)]
#[trusted]
fn verify_model<T: Copy + PartialEq>(iter: &std::slice::Iter<T>, pos: usize, data_len: usize, vis_len: usize) {

}

#[requires(0 <= idx && idx < iter.visited().len())]
#[requires(*iter.visited().lookup(idx) == val)]
#[trusted]
fn verify_visited<T: Copy + PartialEq>(iter: &std::slice::Iter<T>, idx: usize, val: T) {

}

#[requires(slice.len() == 2)]
#[requires(slice[0] == 42)]
#[requires(slice[1] == 777)]
fn verify_slice_iter(slice: &[i32]) {
    let mut iter = slice.iter();

    verify_model(&iter, 0, 2, 0);

    let el = iter.next();
    assert!(el.is_some());
    verify_model(&iter, 1, 2, 1);
    verify_visited(&iter, 0, 42);

    let el = iter.next();
    assert!(el.is_some());
    verify_model(&iter, 2, 2, 2);
    verify_visited(&iter, 0, 42);
    verify_visited(&iter, 1, 777);

    let el = iter.next();
    assert!(el.is_none());
    verify_model(&iter, 2, 2, 2);
    verify_visited(&iter, 0, 42);
    verify_visited(&iter, 1, 777);
}

#[trusted]
#[ensures(iter.model().position == result.model().position)]
#[ensures(iter.model().data.equals(&result.model().data))]
fn snap_iter<'a>(iter: &Iter<'a, i32>) -> Iter<'a, i32> {
    unimplemented!()
}

#[requires(slice.len() == 4)]
#[requires(slice[0] == 42)]
#[requires(slice[1] == 777)]
#[requires(slice[2] == 888)]
#[requires(slice[3] == 13)]
fn verify_while(slice: &[i32]) {
    let mut iter = slice.iter();
    let mut el = None;

    let iter_snap = snap_iter(&iter);

    while {
        el = iter.next();
        el.is_some()
    } {
        body_invariant!(iter_snap.model().data.equals(&iter.model().data));
        body_invariant!(iter.enumerated());
    }

    assert!(iter.next().is_none());
    verify_visited(&iter, 0, 42);
    verify_visited(&iter, 1, 777);
    verify_visited(&iter, 2, 888);
    verify_visited(&iter, 3, 13);
}

#[trusted]
fn main() {

}

// OPTION
#[extern_spec]
impl<T: PartialEq> std::option::Option<T> {
    #[pure]
    #[ensures(self.is_none() == !result)]
    #[ensures(matches ! (* self, Some(_)) == result)]
    pub fn is_some(&self) -> bool;

    #[pure]
    #[ensures(self.is_some() == !result)]
    #[ensures(matches ! (* self, None) == result)]
    pub fn is_none(&self) -> bool;
}

// GHOST SEQUENCE
struct GhostSeq<T> {
    phantom: std::marker::PhantomData<T>,
}
#[refine_trait_spec]
impl<T: Copy> std::clone::Clone for GhostSeq<T> {
    #[trusted]
    fn clone(&self) -> Self { unimplemented!() }
}
impl<T: Copy> Copy for GhostSeq<T> {}
impl<T: Copy + PartialEq> GhostSeq<T> {
    #[pure]
    #[trusted]
    #[requires( 0 <= i && i < self.len() )]
    fn lookup(&self, i: usize) -> T {
        unimplemented!()
    }

    #[pure]
    #[trusted]
    fn len(&self) -> usize {
        unimplemented!()
    }

    predicate! {
        fn equals(&self, other: &GhostSeq<T>) -> bool {
            self.len() == other.len() &&
            forall(|i: usize| (0 <= i && i < self.len()) ==> (self.lookup(i) == other.lookup(i)))
        }
    }

    predicate! {
        fn is_prefix_of(&self, other: &GhostSeq<T>) -> bool {
            self.len() <= other.len() &&
            forall(|i: usize| (0 <= i && i < self.len()) ==> (self.lookup(i) == other.lookup(i)))
        }
    }
}