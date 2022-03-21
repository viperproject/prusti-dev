pub use common::{SpecIdRef, SpecType, SpecificationId};
use log::trace;
use prusti_specs::specifications::common;
use rustc_hir::def_id::{DefId, LocalDefId};
use std::{
    collections::HashMap,
    fmt::{Debug},
};

// TODO hansenj: Restructure this file

#[derive(Debug, Clone)]
#[allow(clippy::large_enum_variant)] // TODO hansenj: Put obligations somewhere else
pub enum SpecificationSet {
    Procedure(WithPossibleObligation<ProcedureSpecification>),
    Loop(LoopSpecification),
}

impl SpecificationSet {
    pub fn empty_procedure_set() -> Self {
        SpecificationSet::Procedure(WithPossibleObligation::WithoutObligation(ProcedureSpecification::empty()))
    }

    pub fn is_procedure(&self) -> bool {
        matches!(self, SpecificationSet::Procedure(_))
    }

    #[track_caller]
    pub fn expect_procedure(&self) -> &WithPossibleObligation<ProcedureSpecification> {
        if let SpecificationSet::Procedure(spec) = self {
            return spec;
        }
        unreachable!("expected Procedure: {:?}", self);
    }

    #[track_caller]
    pub fn as_procedure(&self) -> Option<&WithPossibleObligation<ProcedureSpecification>> {
        if let SpecificationSet::Procedure(spec) = self {
            return Some(spec);
        }
        None
    }

    #[track_caller]
    pub fn expect_mut_procedure(&mut self) -> &mut WithPossibleObligation<ProcedureSpecification> {
        if let SpecificationSet::Procedure(spec) = self {
            return spec;
        }
        unreachable!("expected Procedure: {:?}", self);
    }

    #[track_caller]
    pub fn into_procedure(self) -> WithPossibleObligation<ProcedureSpecification> {
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

// TODO hansenj: Might want to add simplification method, i.e.
// - And(None, Simple(A)) -> Simple(A)
// - And(Simple(A), None) -> Simple(A)
// - And(Simple(A), Simple(A)) -> Simple(A)
// TODO hansenj: Rename (trait Obligation, SpecificationObligation: Can be confusing)
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SpecificationObligationKind {
    /// A specification without obligations
    None,

    /// A specification which may have trait bounds on generics
    ResolveGenericParamTraitBounds,

    /// A consolidated obligation, which is usually the case in trait specification refinement
    Combined(Box<SpecificationObligationKind>, Box<SpecificationObligationKind>), // TODO: Only needed for refinement.
}

/// A specification, such as preconditions or a `#[pure]` annotation.
/// Contains information about the refinement of these specifications.
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
    pub fn is_empty(&self) -> bool {
        matches!(self, SpecificationItem::Empty)
    }

    /// Returns the contained value of this item
    fn get(&self) -> Option<(Option<&T>, &T)> {
        // TODO(tymap): this API is not good: it must be possible to tell that
        //   the result was inherited, as we will e.g. need to rebase our substs
        //   to the trait
        match self {
            SpecificationItem::Empty => None,
            SpecificationItem::Inherited(val) => Some((None, val)),
            SpecificationItem::Inherent(val) => Some((None, val)),
            SpecificationItem::Refined(from, to) => Some((Some(from), to)),
        }
    }

    /// Extracts the refined value out of this item by applying the provided strategy
    pub fn extract_with_strategy<'a, R, S: FnOnce((Option<&'a T>, &'a T)) -> R>(
        &'a self,
        strategy: S,
    ) -> Option<R> {
        self.get().map(strategy)
    }

    /// Uses alternative C as discussed in
    /// https://ethz.ch/content/dam/ethz/special-interest/infk/chair-program-method/pm/documents/Education/Theses/Matthias_Erdin_MA_report.pdf
    /// pp 19-23
    pub fn extract_with_selective_replacement(&self) -> Option<&T> {
        self.extract_with_strategy(|(_, refined)| refined)
    }
}

// TODO hansenj: Test
impl<T: Clone> SpecificationItem<T> {
    pub fn set(&mut self, new_value: T) {
        match self {
            SpecificationItem::Empty => *self = SpecificationItem::Inherent(new_value),
            SpecificationItem::Inherent(val) => *val = new_value,
            SpecificationItem::Refined(_, values) => *values = new_value,
            SpecificationItem::Inherited(inherited) => *self = SpecificationItem::Refined(inherited.clone(), new_value)
        }
    }
}

impl SpecificationItem<bool> {
    pub fn extract_inherit(&self) -> Option<bool> {
        self.extract_with_strategy(|(refined_from, refined)| {
            *(refined_from.unwrap_or(&false)) || *refined
        })
    }
}

impl<T> SpecificationItem<Vec<T>> {
    pub fn extract_with_selective_replacement_iter(&self) -> Box<dyn Iterator<Item = &T> + '_> {
        if let Some(items) = self.extract_with_selective_replacement() {
            return Box::new(items.iter());
        }
        Box::new(std::iter::empty())
    }
}

impl<T: Clone> SpecificationItem<Vec<T>> {
    // TODO hansenj: Test this

    pub fn push(&mut self, value: T) {
        match self {
            SpecificationItem::Empty => *self = SpecificationItem::Inherent(vec![value]),
            SpecificationItem::Inherent(values) => values.push(value),
            SpecificationItem::Refined(_, values) => values.push(value),
            SpecificationItem::Inherited(inherited) => *self = SpecificationItem::Refined(inherited.clone(), vec![value])
        }
    }
}

pub trait Refinable {
    fn refine(self, other: &Self) -> Self
    where
        Self: Sized;
}

// TODO hansenj: Test
impl<T: Refinable> Refinable for Option<T> {
    fn refine(self, other: &Self) -> Self where Self: Sized {
        if let Some(other) = other {
            return self.map(|s| s.refine(other));
        }
        self
    }
}

impl<T: std::fmt::Debug + Clone + PartialEq> Refinable for SpecificationItem<T> {
    fn refine(self, other: &Self) -> Self
    where
        Self: Sized,
    {
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
                Empty | Refined(_, _) => unreachable!(),
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

#[derive(Debug, Clone, PartialEq)]
pub enum WithPossibleObligation<T: PartialEq> {
    WithoutObligation(T),
    WithObligation(SpecificationObligationKind, T, T)
}

// TODO hansenj: Test
// TODO hansenj: Move code
impl Refinable for SpecificationObligationKind {
    fn refine(self, other: &Self) -> Self where Self: Sized {
        if matches!(self, SpecificationObligationKind::None) {
            other.clone()
        } else if matches!(other, SpecificationObligationKind::None) {
            self
        } else {
            SpecificationObligationKind::Combined(Box::new(self), Box::new(other.clone()))
        }
    }
}

// TODO hansenj: Test
// TODO: hansenj: Is this what we want?
impl<T: Refinable+Clone+PartialEq> Refinable for WithPossibleObligation<T> {
    fn refine(self, other: &Self) -> Self where Self: Sized {
        match self {
            WithPossibleObligation::WithoutObligation(self_item) => {
                match other {
                    WithPossibleObligation::WithoutObligation(other_item) =>
                        Self::WithoutObligation(self_item.refine(other_item))
                    ,
                    WithPossibleObligation::WithObligation(other_obligation, other_item, other_alternative) =>
                        Self::WithObligation(other_obligation.clone(), self_item.refine(other_item), other_alternative.clone())
                }
            },
            WithPossibleObligation::WithObligation(self_obligation, self_item, self_alternative) => {
                match other {
                    WithPossibleObligation::WithoutObligation(other_item) =>
                        Self::WithObligation(self_obligation, self_item.refine(other_item), self_alternative)
                    ,
                    WithPossibleObligation::WithObligation(other_obligation, other_item, other_alternative) =>
                        Self::WithObligation(self_obligation.refine(other_obligation), self_item.refine(other_item), self_alternative.refine(other_alternative))
                }
            }
        }
    }
}

// TODO hansenj: Since I introduce obligations, we probably need to make fields non-public, s.t. the obligation is always resolved
#[derive(Debug, Clone, PartialEq)]
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
        use crate::specs::typed::{Refinable, SpecificationItem};
        use SpecificationItem::{Empty, Inherent, Inherited, Refined};

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
}
