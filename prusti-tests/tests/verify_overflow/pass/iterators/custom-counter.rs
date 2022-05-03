// compile-flags: -Penable_iterators=true
// compile-flags: -Penable_ghost_constraints=true

extern crate prusti_contracts;
use prusti_contracts::*;

type IterItemTy = usize;

trait IteratorSpecExt {
    type IterItem;

    predicate! {
        fn enumerated(&self) -> bool;
    }

    predicate! {
        fn completed(&self) -> bool;
    }

    predicate! {
        fn two_state_postcondition(new_self: &Self, old_self: &Self) -> bool;
    }

    predicate! {
        fn describe_result(old_self: &Self, res: &Option<Self::IterItem>) -> bool;
    }
}

pub struct Counter {
    seen: Vec<IterItemTy>,
    count: usize,
    up_to: usize,
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
        ensures(IteratorSpecExt::two_state_postcondition(self, old(self))),
        ensures(IteratorSpecExt::describe_result(old(self), &result))
    ])]
    fn next(&mut self) -> Option<Self::Item>;
}

#[refine_trait_spec]
impl IteratorSpecExt for Counter {
    type IterItem = IterItemTy;

    predicate! {
        fn enumerated(&self) -> bool {
            self.count == vec_len(&self.seen) &&
            forall(
                |i: usize| 0 <= i && i < vec_len(&self.seen) ==> (
                    vec_lookup(&self.seen, i) == i &&
                    vec_contains(&self.seen, i)
                )
            )
        }
    }

    predicate! {
        fn completed(&self) -> bool {
            self.count >= self.up_to
        }
    }

    predicate! {
        fn two_state_postcondition(new_self: &Self, old_self: &Self) -> bool {
            new_self.up_to == old_self.up_to &&
            vec_equals_up_to_idx(&new_self.seen, &old_self.seen, vec_len(&old_self.seen)) &&
            vec_is_subset(&old_self.seen, &new_self.seen) &&

            old_self.completed() == (new_self.count == old_self.count) &&
            !old_self.completed() == (new_self.count == old_self.count + 1)
        }
    }

    predicate! {
        fn describe_result(old_self: &Self, res: &Option<Self::IterItem>) -> bool {
            res.is_some() ==> res.peek() == old_self.count
        }
    }
}

#[refine_trait_spec]
impl Iterator for Counter {
    type Item = IterItemTy;

    // Note: The method body is verified against the ghost constraint!
    #[trusted]
    fn next(&mut self) -> Option<Self::Item> {
        if self.count < self.up_to {
            let res = self.count;
            self.count += 1;
            vec_push(&mut self.seen, res);
            return Some(res);
        }
        None
    }
}

fn verify_direct_traversal() {
    let mut c = Counter {
        count: 0,
        up_to: 3,
        seen: vec_create(),
    };

    let el = c.next();
    assert!(el.is_some());
    assert!(el.peek() == 0);

    let el = c.next();
    assert!(el.is_some());
    assert!(el.peek() == 1);

    let el = c.next();
    assert!(el.is_some());
    assert!(el.peek() == 2);

    let el = c.next();
    assert!(el.is_none());

    let el = c.next();
    assert!(el.is_none());
}

#[requires(
    c.count == 0 &&
    c.up_to == 3 &&
    vec_len(&c.seen) == 0
)]
// #[ensures(is_max_of(result, &c.seen))] // TODO iterators: This causes a Prusti crash
fn verify_get_max(mut c: Counter) -> IterItemTy {
    let mut el: Option<IterItemTy> = None;
    el = c.next();
    assert!(el.is_some());
    let mut the_max = el.peek();

    while {
        el = c.next();
        el.is_some()
    } {
        let val = el.peek();
        if val >= the_max {
            the_max = val;
        }

        body_invariant!(c.enumerated());
        body_invariant!(vec_contains(&c.seen, the_max));
        body_invariant!(is_max_of(the_max, &c.seen));
    }
    assert!(c.next().is_none());
    the_max
}


predicate! {
    fn is_max_of(potential_max: IterItemTy, v: &VecType) -> bool {
        forall(
            |i: usize| (0 <= i && i < vec_len(v)) ==> potential_max >= vec_lookup(v, i)
        )
    }
}

fn main() {}

// VEC<T>
type VecInnerType = IterItemTy;
type VecType = Vec<VecInnerType>;

#[trusted]
#[ensures(vec_len(v) == old(vec_len(v)) + 1)]
#[ensures(vec_contains(v, elem))]
#[ensures(vec_lookup(v, vec_len(v) - 1) == elem)]
#[ensures(vec_equals_up_to_idx(v, old(v), old(vec_len(v))))]
#[ensures(vec_is_subset(old(v), v))]
fn vec_push(v: &mut VecType, elem: VecInnerType) {
    v.push(elem);
}

#[pure]
#[trusted]
fn vec_contains(v: &VecType, elem: VecInnerType) -> bool {
    v.contains(&elem)
}

#[pure]
#[trusted]
fn vec_len(v: &VecType) -> usize {
    v.len()
}

#[pure]
#[trusted]
#[requires(i < vec_len(v))]
#[ensures(vec_contains(v, result))]
fn vec_lookup(v: &VecType, i: usize) -> VecInnerType {
    v[i]
}

#[trusted]
#[ensures(vec_len(&result) == 0)]
fn vec_create() -> VecType {
    unimplemented!();
}

predicate! {
    fn vec_equals(v1: &VecType, v2: &VecType) -> bool {
        vec_len(v1) == vec_len(v2) &&
        forall(
            |i: usize| i < vec_len(v1) ==> vec_lookup(v1, i) == vec_lookup(v2, i)
        ) &&
        forall(
            |el: usize| vec_contains(v1, el) == vec_contains(v2, el)
        )
    }
}

predicate! {
    fn vec_equals_up_to_idx(v1: &VecType, v2: &VecType, up_to_idx: usize) -> bool {
        vec_len(v1) >= up_to_idx && vec_len(v2) >= up_to_idx &&
        forall(
            |i: usize| i < up_to_idx ==> vec_lookup(v1, i) == vec_lookup(v2, i)
        )
    }
}

predicate! {
    fn vec_is_subset(subset: &VecType, superset: &VecType) -> bool {
        forall(
            |el: usize| vec_contains(subset, el) ==> vec_contains(superset, el)
        )
    }
}

// OPTION
#[extern_spec]
impl<T: PartialEq> std::option::Option<T> {
    #[pure]
    #[ensures(matches ! (* self, Some(_)) == result)]
    pub fn is_some(&self) -> bool;

    #[pure]
    #[ensures(self.is_some() == ! result)]
    #[ensures(matches ! (* self, None) == result)]
    pub fn is_none(&self) -> bool;
}

trait OptionPeeker<T: Copy> {
    #[pure]
    fn peek(&self) -> T;
}

#[refine_trait_spec]
impl<T: Copy> OptionPeeker<T> for Option<T> {
    #[pure]
    #[requires(self.is_some())]
    fn peek(&self) -> T {
        match self {
            Some(v) => *v,
            None => unreachable!(),
        }
    }
}