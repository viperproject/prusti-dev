use prusti_specs::specifications::common;
use rustc_hir::def_id::{DefId, LocalDefId};
use std::collections::HashMap;
use std::fmt::Debug;
use log::trace;
pub use common::{SpecType, SpecificationId, SpecIdRef};


#[derive(Debug, Clone)]
pub enum SpecificationSet {
    Procedure(ProcedureSpecification),
    Loop(LoopSpecification),
}

impl SpecificationSet {
    pub fn empty_procedure_set() -> Self {
        SpecificationSet::Procedure(ProcedureSpecification::empty())
    }

    pub fn is_procedure(&self) -> bool {
        matches!(self, SpecificationSet::Procedure(_))
    }

    #[track_caller]
    pub fn expect_procedure(&self) -> &ProcedureSpecification {
        if let SpecificationSet::Procedure(spec) = self {
            return spec;
        }
        unreachable!("expected Procedure: {:?}", self);
    }

    #[track_caller]
    pub fn as_procedure(&self) -> Option<&ProcedureSpecification> {
        if let SpecificationSet::Procedure(spec) = self {
            return Some(spec);
        }
        None
    }

    #[track_caller]
    pub fn expect_mut_procedure(&mut self) -> &mut ProcedureSpecification {
        if let SpecificationSet::Procedure(spec) = self {
            return spec;
        }
        unreachable!("expected Procedure: {:?}", self);
    }

    #[track_caller]
    pub fn into_procedure(self) -> ProcedureSpecification {
        if let SpecificationSet::Procedure(spec) = self {
            return spec;
        }
        unreachable!("expected Procedure: {:?}", self);
    }

    #[track_caller]
    pub fn expect_loop(&self) -> &LoopSpecification {
        if let SpecificationSet::Loop(spec) = self {
            return spec;
        }
        unreachable!("expected Loop: {:?}", self);
    }

    #[track_caller]
    pub fn as_loop(&self) -> Option<&LoopSpecification> {
        if let SpecificationSet::Loop(spec) = self {
            return Some(spec);
        }
        None
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Pledge {
    pub reference: Option<()>, // TODO: pledge references
    pub lhs: Option<LocalDefId>,
    pub rhs: LocalDefId,
}

/// A specification, such as preconditions or a `#[pure]` annotation.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum SpecificationItem<T> {
    /// Represents an empty specification, i.e. when the user has not defined the property
    Empty,

    /// Represents a specification typed by the user
    Inherent(T),

    /// Represents a specification which was inherited from somewhere (e.g. from a trait method)
    Inherited(T),

    /// Represents an item which was refined
    /// This happens for example if the user annotates a trait method and its implementation method
    /// with a precondition. This variant then holds the trait's precondition and the impl's precondition.
    Refined(T, T),
}

impl<T> SpecificationItem<T> {
    /// Returns the contained value of this item
    pub fn get(&self) -> Option<(Option<&T>, &T)> {
        match self {
            SpecificationItem::Empty => None,
            SpecificationItem::Inherited(val) => Some((None, val)),
            SpecificationItem::Inherent(val) => Some((None, val)),
            SpecificationItem::Refined(from, to) => Some((Some(from), to))
        }
    }

    pub fn get_or<'a>(&'a self, default: &'a T) -> (Option<&'a T>, &'a T) {
        self.get().unwrap_or((None, default))
    }

    pub fn is_empty(&self) -> bool {
        matches!(self, SpecificationItem::Empty)
    }
}

impl<T> SpecificationItem<Vec<T>> {
    pub fn iter(&self) -> SpecItemIter<'_, T> {
        if self.is_empty() {
            SpecItemIter::empty()
        } else {
            SpecItemIter::new(self.get().map(|(_, val)| val).unwrap())
        }
    }
}

pub struct SpecItemIter<'a, T> {
    items: Option<&'a Vec<T>>,
    pos: usize,
}

impl<'a, T> SpecItemIter<'a, T> {
    fn empty() -> Self {
        SpecItemIter {
            items: None,
            pos: 0,
        }
    }

    fn new(items: &'a Vec<T>) -> Self {
        SpecItemIter {
            items: Some(items),
            pos: 0,
        }
    }

    pub fn first(&self) -> Option<&'a T> {
        self.items.and_then(|items| items.first())
    }
}

impl<'a, T> Iterator for SpecItemIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(items) = self.items {
            if self.pos >= items.len() {
                return None;
            }
            let next = items.get(self.pos);
            self.pos += 1;
            return next;
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self.items {
            Some(items) => {
                let remaining = items.len() - self.pos;
                (remaining, Some(remaining))
            },
            None => (0, Some(0))
        }
    }
}

impl<'a, T> ExactSizeIterator for SpecItemIter<'a, T> {
}

pub trait Refinable {
    fn refine(self, other: &Self) -> Self where Self: Sized;
}

impl<T: std::fmt::Debug + Clone + PartialEq> Refinable for SpecificationItem<T> {

    fn refine(self, other: &Self) -> Self where Self: Sized {
        use SpecificationItem::*;

        if self.is_empty() && other.is_empty() {
            return Empty;
        }

        trace!("Refining {:?} with {:?}", self, other);

        if let Refined(from, _) = &self {
            match other {
                Refined(_, _) => panic!("Can not refine this refined item"),
                Inherent(with) if from != with => panic!("Can not refine this refined item"),
                Inherited(with) if from != with => panic!("Can not refine this refined item"),
                _ => {}
            }
        }

        if matches!(other, Refined(_, _)) {
            panic!("Can not refine with a refined item");
        }

        let refined = if self.is_empty() && !other.is_empty() {
            match other.clone() {
                Inherent(val) => Inherited(val),
                Inherited(val) => Inherited(val),
                Empty | Refined(_, _) => unreachable!()
            }
        } else if !self.is_empty() && !other.is_empty() {
            let (_, self_val) = self.get().unwrap();
            let (_, other_val) = other.get().unwrap();
            Refined(other_val.clone(), self_val.clone())
        } else {
            self
        };

        trace!("\t -> {:?}", refined);
        refined
    }
}

impl Refinable for ProcedureSpecification {
    fn refine(self, other: &Self) -> Self {
        ProcedureSpecification {
            pres: self.pres.refine(&other.pres),
            posts: self.posts.refine(&other.posts),
            pledges: self.pledges.refine(&other.pledges),
            predicate_body: self.predicate_body.refine(&other.predicate_body),
            pure: self.pure.refine(&other.pure),
            trusted: self.trusted.refine(&other.trusted),
        }
    }
}

impl Refinable for SpecificationSet {
    fn refine(self, other: &Self) -> Self {
        if self.is_procedure() && other.is_procedure() {
            let self_proc = self.into_procedure();
            let other_proc = other.expect_procedure();
            let refined = self_proc.refine(other_proc);
            return SpecificationSet::Procedure(refined);
        }
        self
    }
}


#[derive(Debug, Clone)]
pub struct ProcedureSpecification {
    pub pres: SpecificationItem<Vec<LocalDefId>>,
    pub posts: SpecificationItem<Vec<LocalDefId>>,
    pub pledges: SpecificationItem<Vec<Pledge>>,
    pub predicate_body: SpecificationItem<LocalDefId>,
    pub pure: SpecificationItem<bool>,
    pub trusted: SpecificationItem<bool>,
}

impl ProcedureSpecification {
    pub fn empty() -> Self {
        ProcedureSpecification {
            pres: SpecificationItem::Empty,
            posts: SpecificationItem::Empty,
            pledges: SpecificationItem::Empty,
            predicate_body: SpecificationItem::Empty,
            pure: SpecificationItem::Inherent(false),
            trusted: SpecificationItem::Inherent(false),
        }
    }
}

#[derive(Debug, Clone)]
pub struct LoopSpecification {
    pub invariant: LocalDefId,
}



/// A map of specifications keyed by crate-local DefIds.
#[derive(Default, Debug, Clone)]
pub struct DefSpecificationMap {
    pub specs: HashMap<LocalDefId, SpecificationSet>,
    pub extern_specs: HashMap<DefId, LocalDefId>,
}


impl DefSpecificationMap {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn get(&self, def_id: &DefId) -> Option<&SpecificationSet> {
        let id = if let Some(spec_id) = self.extern_specs.get(def_id) {
            *spec_id
        } else {
            def_id.as_local()?
        };
        self.specs.get(&id)
    }
}

#[cfg(test)]
mod tests {
    mod refinement {
        use crate::specs::typed::Refinable;
        use crate::specs::typed::SpecificationItem;
        use SpecificationItem::{Refined, Empty, Inherent, Inherited};

        macro_rules! refine_success_tests {
            ($($name:ident: $value:expr,)*) => {
            $(
                #[test]
                fn $name() {
                    let (from, with, expected) = $value;
                    let result = from.refine(&with);
                    assert_eq!(result, expected);
                }
            )*
            }
        }

        macro_rules! refine_fail_tests {
            ($($name:ident: $value:expr,)*) => {
            $(
                #[test]
                #[should_panic]
                fn $name() {
                    let (from, with) = $value;
                    from.refine(&with);
                }
            )*
            }
        }

        refine_success_tests!(
            refine_from_empty_with_empty: (Empty::<i32>, Empty::<i32>, Empty::<i32>),
            refine_from_empty_with_inherent: (Empty, Inherent(1), Inherited(1)),
            refine_from_empty_with_inherited: (Empty, Inherited(1), Inherited(1)),
        );

        refine_fail_tests!(
            refine_from_empty_with_refined: (Empty, Refined(1,2)),
        );

        refine_success_tests!(
            refine_from_inherent_with_empty: (Inherent(1), Empty, Inherent(1)),
            refine_from_inherent_with_inherent: (Inherent(1), Inherent(2), Refined(2, 1)),
            refine_from_inherent_with_inherited: (Inherent(1), Inherited(2), Refined(2, 1)),
        );

        refine_fail_tests!(
            refine_from_inherent_with_refined: (Inherent(1), Refined(2,3)),
        );

        refine_success_tests!(
            refine_from_inherited_with_empty: (Inherited(1), Empty, Inherited(1)),
            refine_from_inherited_with_inherent: (Inherited(1), Inherent(2), Refined(2, 1)),
            refine_from_inherited_with_inherited: (Inherited(1), Inherited(2), Refined(2, 1)),
        );

        refine_fail_tests!(
            refine_from_inherited_with_refined: (Inherited(1), Refined(2,3)),
        );


        refine_success_tests!(
            refine_from_refined_with_empty: (Refined(1, 2), Empty, Refined(1, 2)),
            // Generally, we can not refine a refined item.
            // In this case it is possible, because the refined-from part does not change.
            refine_from_refined_with_inherited_refinable: (Refined(1, 2), Inherited(1), Refined(1, 2)),
        );

        refine_fail_tests!(
            refine_from_refined_with_inherent: (Refined(1, 2), Inherent(3)),
            refine_from_refined_with_inherited_unrefinable: (Refined(1, 2), Inherited(3)),
            refine_from_refined_with_refined: (Refined(1, 2), Refined(3,4)),
        );
    }

    mod spec_iter {
        use crate::specs::typed::SpecificationItem;

        #[test]
        fn length() {
            let v = vec![1,2,3];
            let spec_item = SpecificationItem::Inherent(v);
            let mut iter = spec_item.iter();
            assert_eq!(iter.len(), 3);
            assert!(iter.next().is_some());
            assert_eq!(iter.len(), 2);
            assert!(iter.next().is_some());
            assert_eq!(iter.len(), 1);
            assert!(iter.next().is_some());
            assert_eq!(iter.len(), 0);
            assert!(iter.next().is_none());
            assert_eq!(iter.len(), 0);
            assert!(iter.next().is_none());
        }
    }
}