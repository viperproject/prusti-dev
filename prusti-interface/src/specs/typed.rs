pub use common::{SpecIdRef, SpecType, SpecificationId};
use log::trace;
use prusti_specs::specifications::common;
use rustc_hir::def_id::{DefId, LocalDefId};
use std::{collections::HashMap, fmt::Debug};
use std::fmt::{Display, Formatter};


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

impl SpecificationItem<bool> {
    pub fn extract_inherit(&self) -> Option<bool> {
        self.extract_with_strategy(|(refined_from, refined)| *(refined_from.unwrap_or(&false)) || *refined)
    }
}

#[derive(Debug)]
pub enum ProcedureSpecificationKindError {
    /// Occurs whenever the relation between [ProcedureSpecificationKind]s is violated.
    /// The relation is: predicates ⊂ pure functions ⊂ impure functions
    /// However, we can not refine a non-predicate to a predicate, since predicates are not callable.
    /// This validation is not automatically performed during refinement. It needs to be invoked
    /// manually with [SpecificationItem<ProcedureSpecificationKind>::validate]
    InvalidSpecKindRefinement(ProcedureSpecificationKind, ProcedureSpecificationKind)
}

impl SpecificationItem<ProcedureSpecificationKind> {
    pub fn is_pure(&self) -> Result<bool, ProcedureSpecificationKindError> {
        self.validate()?;

        Ok(matches!(self.extract_with_selective_replacement(),
                Some(ProcedureSpecificationKind::Pure) | Some(ProcedureSpecificationKind::Predicate(_))))
    }

    pub fn is_impure(&self) -> Result<bool, ProcedureSpecificationKindError> {
        self.validate()?;

        Ok(match self.extract_with_selective_replacement() {
            Some(refined) => matches!(refined, ProcedureSpecificationKind::Impure),
            _ => true,
        })
    }

    pub fn get_predicate_body(&self) -> Result<Option<&LocalDefId>, ProcedureSpecificationKindError> {
        self.validate()?;

        Ok(match self.extract_with_selective_replacement() {
            Some(ProcedureSpecificationKind::Predicate(pred_id)) => Some(pred_id),
            _ => None
        })
    }

    /// Ensures that refined [ProcedureSpecificationKind]s are valid.
    /// See [ProcedureSpecificationKindError] for detailed error descriptions.
    pub fn validate(&self) -> Result<(), ProcedureSpecificationKindError> {
        use ProcedureSpecificationKind::*;
        if let SpecificationItem::Refined(base, refined) = self {
            match (base, refined) {
                (Impure, Impure) |
                (Impure, Pure) |
                (Pure, Pure) |
                (Predicate(_), Predicate(_)) => Ok(()),
                _ => Err(ProcedureSpecificationKindError::InvalidSpecKindRefinement(*base, *refined))
            }
        } else {
            Ok(())
        }
    }
}

impl<T> SpecificationItem<Vec<T>> {
    pub fn new(vec: Vec<T>) -> Self {
        if vec.is_empty() {
            SpecificationItem::Empty
        } else {
            SpecificationItem::Inherent(vec)
        }
    }

    pub fn extract_with_selective_replacement_iter(&self) -> Box<dyn Iterator<Item = &T> + '_> {
        if let Some(items) = self.extract_with_selective_replacement() {
            return Box::new(items.iter());
        }
        Box::new(std::iter::empty())
    }
}

pub trait Refinable {
    fn refine(self, other: &Self) -> Self where Self: Sized;
}

impl<T: Debug + Clone + PartialEq> Refinable for SpecificationItem<T> {
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
            kind: self.kind.refine(&other.kind),
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
    pub kind: SpecificationItem<ProcedureSpecificationKind>,
    pub pres: SpecificationItem<Vec<LocalDefId>>,
    pub posts: SpecificationItem<Vec<LocalDefId>>,
    pub pledges: SpecificationItem<Vec<Pledge>>,
    pub trusted: SpecificationItem<bool>,
}

impl ProcedureSpecification {
    pub fn empty() -> Self {
        ProcedureSpecification {
            kind: SpecificationItem::Empty,
            pres: SpecificationItem::Empty,
            posts: SpecificationItem::Empty,
            pledges: SpecificationItem::Empty,
            trusted: SpecificationItem::Inherent(false),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum ProcedureSpecificationKind {
    Impure,
    Pure,
    /// The specification is a predicate with the enclosed body
    Predicate(LocalDefId),
}

impl Display for ProcedureSpecificationKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ProcedureSpecificationKind::Impure => write!(f, "Impure"),
            ProcedureSpecificationKind::Pure => write!(f, "Pure"),
            ProcedureSpecificationKind::Predicate(_) => write!(f, "Predicate"),
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
    use super::*;

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

    mod specification_item_kind {
        use super::*;
        use SpecificationItem::*;
        use ProcedureSpecificationKind::*;

        const FAKE_LOCAL_DEF_ID: LocalDefId = rustc_hir::def_id::CRATE_DEF_ID;

        mod invalid_refinements {
            use super::*;

            #[test]
            fn refine_impure_with_predicate() {
                let item = Refined(Impure, Predicate(FAKE_LOCAL_DEF_ID));
                let result = item.validate().expect_err("Expected error");
                assert!(matches!(result, ProcedureSpecificationKindError::InvalidSpecKindRefinement(_, _)));
            }

            #[test]
            fn refine_pure_with_impure() {
                let item = Refined(Pure, Impure);
                let result = item.validate().expect_err("Expected error");
                assert!(matches!(result, ProcedureSpecificationKindError::InvalidSpecKindRefinement(_, _)));
            }

            #[test]
            fn refine_pure_with_predicate() {
                let item = Refined(Pure, Predicate(FAKE_LOCAL_DEF_ID));
                let result = item.validate().expect_err("Expected error");
                assert!(matches!(result, ProcedureSpecificationKindError::InvalidSpecKindRefinement(_, _)));
            }

            #[test]
            fn refine_predicate_with_pure() {
                let item = Refined(Predicate(FAKE_LOCAL_DEF_ID), Pure);
                let result = item.validate().expect_err("Expected error");
                assert!(matches!(result, ProcedureSpecificationKindError::InvalidSpecKindRefinement(_, _)));
            }

            #[test]
            fn refine_predicate_with_impure() {
                let item = Refined(Predicate(FAKE_LOCAL_DEF_ID), Impure);
                let result = item.validate().expect_err("Expected error");
                assert!(matches!(result, ProcedureSpecificationKindError::InvalidSpecKindRefinement(_, _)));
            }
        }

        mod is_impure {
            use super::*;

            macro_rules! impure_checks {
                    ($($name:ident: $value:expr,)*) => {
                        $(
                            #[test]
                            fn $name() {
                                let (item, expected) = $value;
                                let item: SpecificationItem<ProcedureSpecificationKind> = item;
                                let result = item.is_impure().expect("Expected impure");
                                assert_eq!(result, expected);
                            }
                        )*
                    }
                }

            impure_checks!(
                    empty: (Empty, true),
                    inherent_impure: (Inherent(Impure), true),
                    inherent_pure: (Inherent(Pure), false),
                    inherent_predicate: (Inherent(Predicate(FAKE_LOCAL_DEF_ID)), false),
                    inherited_impure: (Inherited(Impure), true),
                    inherited_pure: (Inherited(Pure), false),
                    inherited_predicate: (Inherited(Predicate(FAKE_LOCAL_DEF_ID)), false),
                    refined_impure_parent_impure_child: (Refined(Impure, Impure), true),
                    refined_impure_parent_pure_child: (Refined(Impure, Pure), false),
                    refined_pure_parent_with_pure_child: (Refined(Pure, Pure), false),
                    refined_predicate_parent_with_predicate_child: (Refined(Predicate(FAKE_LOCAL_DEF_ID), Predicate(FAKE_LOCAL_DEF_ID)), false),
            );
        }

        mod is_pure {
            use super::*;

            macro_rules! pure_checks {
                    ($($name:ident: $value:expr,)*) => {
                        $(
                            #[test]
                            fn $name() {
                                let (item, expected) = $value;
                                let item: SpecificationItem<ProcedureSpecificationKind> = item;
                                let result = item.is_pure().expect("Expected pure");
                                assert_eq!(result, expected);
                            }
                        )*
                    }
                }

            pure_checks!(
                    empty: (Empty, false),
                    inherent_impure: (Inherent(Impure), false),
                    inherent_pure: (Inherent(Pure), true),
                    inherent_predicate: (Inherent(Predicate(FAKE_LOCAL_DEF_ID)), true),
                    inherited_impure: (Inherited(Impure), false),
                    inherited_pure: (Inherited(Pure), true),
                    inherited_predicate: (Inherited(Predicate(FAKE_LOCAL_DEF_ID)), true),
                    refined_impure_parent_impure_child: (Refined(Impure, Impure), false),
                    refined_impure_parent_pure_child: (Refined(Impure, Pure), true),
                    refined_pure_parent_with_pure: (Refined(Pure, Pure), true),
                    refined_predicate_parent_with_predicate_child: (Refined(Predicate(FAKE_LOCAL_DEF_ID), Predicate(FAKE_LOCAL_DEF_ID)), true),
            );
        }

        mod is_predicate {
            use super::*;

            macro_rules! predicate_checks {
                    ($($name:ident: $value:expr,)*) => {
                        $(
                            #[test]
                            fn $name() {
                                let (item, expected) = $value;
                                let item: SpecificationItem<ProcedureSpecificationKind> = item;
                                let result = item.get_predicate_body().expect("Expected predicate");
                                assert_eq!(result.is_some(), expected);
                            }
                        )*
                    }
                }

            predicate_checks!(
                    empty: (Empty, false),
                    inherent_impure: (Inherent(Impure), false),
                    inherent_pure: (Inherent(Pure), false),
                    inherent_predicate: (Inherent(Predicate(FAKE_LOCAL_DEF_ID)), true),
                    inherited_impure: (Inherited(Impure), false),
                    inherited_pure: (Inherited(Pure), false),
                    inherited_predicate: (Inherited(Predicate(FAKE_LOCAL_DEF_ID)), true),
                    refined_impure_parent_impure_child: (Refined(Impure, Impure), false),
                    refined_impure_parent_pure_child: (Refined(Impure, Pure), false),
                    refined_pure_parent_with_pure_child: (Refined(Pure, Pure), false),
                    refined_predicate_parent_with_predicate_child: (Refined(Predicate(FAKE_LOCAL_DEF_ID), Predicate(FAKE_LOCAL_DEF_ID)), true),
            );
        }
    }
}
