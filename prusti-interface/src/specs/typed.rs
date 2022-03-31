use crate::{environment::Environment, utils::has_trait_bounds_ghost_constraint};
pub use common::{SpecIdRef, SpecType, SpecificationId};
use log::trace;
use prusti_specs::specifications::common;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::{DefId, LocalDefId};
use std::{collections::HashMap, fmt::Debug};

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
    pub proc_specs: HashMap<LocalDefId, SpecsWithConstraints<ProcedureSpecification>>,
    pub loop_specs: HashMap<LocalDefId, SpecsWithConstraints<LoopSpecification>>,
    pub extern_specs: HashMap<DefId, LocalDefId>,
}

impl DefSpecificationMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get_loop_spec(&self, def_id: &DefId) -> Option<&SpecsWithConstraints<LoopSpecification>> {
        let id = self.map_to_spec(def_id)?;
        self.loop_specs.get(&id)
    }

    pub fn get_proc_spec(&self, def_id: &DefId) -> Option<&SpecsWithConstraints<ProcedureSpecification>> {
        let id = self.map_to_spec(def_id)?;
        self.proc_specs.get(&id)
    }

    fn map_to_spec(&self, def_id: &DefId) -> Option<LocalDefId> {
        if let Some(spec_id) = self.extern_specs.get(def_id) {
            Some(*spec_id)
        } else {
            def_id.as_local()
        }
    }
}

#[derive(Default, Debug, Clone)]
pub struct SpecsWithConstraints<T> {
    /// The base specification which has no constraints
    pub base_spec: T,

    /// Specs which are active when the corresponding [SpecConstraintKind] holds on callsite
    pub specs_with_constraints: FxHashMap<SpecConstraintKind, T>,
}

impl<T> SpecsWithConstraints<T> {
    pub fn new(spec: T) -> Self {
        Self {
            base_spec: spec,
            specs_with_constraints: FxHashMap::default(),
        }
    }
}

impl SpecsWithConstraints<ProcedureSpecification> {
    pub fn add_precondition<'tcx>(&mut self, pre: LocalDefId, env: &Environment<'tcx>) {
        match self.get_constraint(pre, env) {
            None => {
                self.base_spec.pres.push(pre);
                // Preconditions are explicitly not copied (as opposed to postconditions)
                // This would always violate behavioral subtyping rules
            }
            Some(obligation) => {
                self.get_partitioned_mut(obligation).pres.push(pre);
            }
        }
    }

    pub fn add_postcondition<'tcx>(&mut self, post: LocalDefId, env: &Environment<'tcx>) {
        match self.get_constraint(post, env) {
            None => {
                self.base_spec.posts.push(post);
                self.specs_with_constraints.values_mut().for_each(|s| s.posts.push(post));
            }
            Some(obligation) => {
                self.get_partitioned_mut(obligation).posts.push(post);
            }
        }
    }

    pub fn add_pledge(&mut self, pledge: Pledge) {
        self.base_spec.pledges.push(pledge.clone());
        self.specs_with_constraints
            .values_mut()
            .for_each(|s| s.pledges.push(pledge.clone()));
    }

    pub fn set_trusted(&mut self, trusted: bool) {
        self.base_spec.trusted.set(trusted);
        self.specs_with_constraints.values_mut().for_each(|s| s.trusted.set(trusted));
    }

    pub fn set_pure(&mut self, pure: bool) {
        self.base_spec.pure.set(pure);
        self.specs_with_constraints.values_mut().for_each(|s| s.pure.set(pure));
    }

    pub fn set_predicate(&mut self, predicate_id: LocalDefId) {
        self.base_spec.predicate_body.set(predicate_id);
        self.specs_with_constraints
            .values_mut()
            .for_each(|s| s.predicate_body.set(predicate_id));
    }

    fn get_partitioned_mut(
        &mut self,
        obligation: SpecConstraintKind,
    ) -> &mut ProcedureSpecification {
        self.specs_with_constraints
            .entry(obligation)
            .or_insert_with(|| self.base_spec.clone())
    }

    /// Note: First wins, we do currently support not multiple constraints
    fn get_constraint<'tcx>(
        &self,
        spec: LocalDefId,
        env: &Environment<'tcx>,
    ) -> Option<SpecConstraintKind> {
        let attrs = env.tcx().get_attrs(spec.to_def_id());
        if has_trait_bounds_ghost_constraint(attrs) {
            return Some(SpecConstraintKind::ResolveGenericParamTraitBounds);
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

    pub fn expect_empty_or_inherent(&self) -> Option<&T> {
        match self {
            SpecificationItem::Empty => None,
            SpecificationItem::Inherent(item) => Some(item),
            _ => unreachable!(),
        }
    }

    pub fn expect_inherent(&self) -> &T {
        match self {
            SpecificationItem::Inherent(item) => item,
            _ => unreachable!(),
        }
    }

    pub fn expect_inherited(&self) -> &T {
        match self {
            SpecificationItem::Inherited(item) => item,
            _ => unreachable!(),
        }
    }

    pub fn expect_refined(&self) -> (&T, &T) {
        match self {
            SpecificationItem::Refined(a, b) => (a, b),
            _ => unreachable!(),
        }
    }
}

impl<T: Clone> SpecificationItem<T> {
    pub fn set(&mut self, new_value: T) {
        match self {
            SpecificationItem::Empty => *self = SpecificationItem::Inherent(new_value),
            SpecificationItem::Inherent(val) => *val = new_value,
            SpecificationItem::Refined(_, values) => *values = new_value,
            SpecificationItem::Inherited(inherited) => {
                *self = SpecificationItem::Refined(inherited.clone(), new_value)
            }
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
    pub fn push(&mut self, value: T) {
        match self {
            SpecificationItem::Empty => *self = SpecificationItem::Inherent(vec![value]),
            SpecificationItem::Inherent(values) => values.push(value),
            SpecificationItem::Refined(_, values) => values.push(value),
            SpecificationItem::Inherited(inherited) => {
                *self = SpecificationItem::Refined(inherited.clone(), vec![value])
            }
        }
    }
}

pub trait Refinable {
    fn refine(self, other: &Self) -> Self
    where
        Self: Sized;
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SpecConstraintKind {
    ResolveGenericParamTraitBounds,
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

    mod specification_item {
        use crate::specs::typed::SpecificationItem;

        #[test]
        fn set_value_of_empty() {
            let mut item: SpecificationItem<i32> = SpecificationItem::Empty;
            item.set(1);
            assert!(matches!(item, SpecificationItem::Inherent(1)));
        }

        #[test]
        fn set_value_of_inherent() {
            let mut item = SpecificationItem::Inherent(1);
            item.set(2);
            assert!(matches!(item, SpecificationItem::Inherent(2)));
        }

        #[test]
        fn set_value_of_inherited() {
            let mut item = SpecificationItem::Inherited(1);
            item.set(2);
            assert!(matches!(item, SpecificationItem::Refined(1, 2)));
        }

        #[test]
        fn set_value_of_refined() {
            let mut item = SpecificationItem::Refined(1, 2);
            item.set(3);
            assert!(matches!(item, SpecificationItem::Refined(1, 3)));
        }

        #[test]
        fn push_value_to_empty() {
            let mut item: SpecificationItem<Vec<i32>> = SpecificationItem::Empty;
            item.push(1);
            let vec = item.expect_inherent();
            assert_eq!(vec, &vec![1]);
        }

        #[test]
        fn push_value_to_inherent() {
            let mut item = SpecificationItem::Inherent(vec![1]);
            item.push(2);
            let vec = item.expect_inherent();
            assert_eq!(vec, &vec![1, 2]);
        }

        #[test]
        fn push_value_to_inherited() {
            let mut item = SpecificationItem::Inherited(vec![1, 2]);
            item.push(3);
            let (refined_from, refined) = item.expect_refined();
            assert_eq!(refined_from, &vec![1, 2]);
            assert_eq!(refined, &vec![3]);
        }

        #[test]
        fn push_value_to_refined() {
            let mut item = SpecificationItem::Refined(vec![1, 2], vec![3, 4]);
            item.push(5);
            let (refined_from, refined) = item.expect_refined();
            assert_eq!(refined_from, &vec![1, 2]);
            assert_eq!(refined, &vec![3, 4, 5]);
        }
    }
}
