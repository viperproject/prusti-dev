use super::borrows::BorrowInfo;
use crate::encoder::places;
use prusti_interface::{environment::Environment, specs::typed};
use prusti_rustc_interface::{
    hir::{
        def_id::{DefId, LocalDefId},
        Mutability,
    },
    middle::{mir, ty::subst::SubstsRef},
};
use rustc_hash::FxHashMap;
use std::fmt;

/// Contract of a specific procedure. It is a separate struct from a
/// general procedure info because we want to be able to translate
/// procedure calls before translating call targets.
#[derive(Clone, Debug)]
pub struct ProcedureContractGeneric<L, P>
where
    L: fmt::Debug,
    P: fmt::Debug,
{
    /// Definition ID of the procedure to which the contract is attached.
    pub def_id: DefId,
    /// Formal arguments for which we should have permissions in the
    /// precondition. This includes both borrows and moved in values.
    /// For example, if `_2` is in the vector, this means that we have
    /// `T(_2)` in the precondition.
    pub args: Vec<L>,
    /// Borrowed arguments that are directly returned to the caller (not via
    /// a magic wand). For example, if `*(_2.1).0` is in the vector, this
    /// means that we have `T(old[precondition](_2.1.ref.0))` in the
    /// postcondition. It also includes information about the mutability
    /// of the original reference.
    pub returned_refs: Vec<(P, Mutability)>,
    /// The returned value for which we should have permission in
    /// the postcondition.
    pub returned_value: L,
    /// Magic wands passed out of the procedure.
    /// TODO: Implement support for `blocked_lifetimes` via nested magic wands.
    pub borrow_infos: Vec<BorrowInfo<P>>,
    /// The functional specification: precondition and postcondition
    pub specification: typed::ProcedureSpecification,
}

impl<L: fmt::Debug, P: fmt::Debug> ProcedureContractGeneric<L, P> {
    pub fn functional_precondition<'a, 'tcx>(
        &'a self,
        env: &'a Environment<'tcx>,
        substs: SubstsRef<'tcx>,
    ) -> Vec<(LocalDefId, SubstsRef<'tcx>)> {
        match &self.specification.pres {
            typed::SpecificationItem::Empty => vec![],
            typed::SpecificationItem::Inherent(pres)
            | typed::SpecificationItem::Refined(_, pres) => pres
                .iter()
                .map(|inherent_def_id| (*inherent_def_id, substs))
                .collect(),
            typed::SpecificationItem::Inherited(pres) => pres
                .iter()
                .map(|inherited_def_id| {
                    (
                        *inherited_def_id,
                        // This uses the substs of the current method and
                        // resolves them to the substs of the trait; however,
                        // we are actually resolving to a specification item.
                        // This works because the generics of the specification
                        // items are the same as the generics of the method on
                        // which they are declared.
                        env.find_trait_method_substs(self.def_id, substs).unwrap().1,
                    )
                })
                .collect(),
        }
    }

    pub fn functional_postcondition<'a, 'tcx>(
        &'a self,
        env: &'a Environment<'tcx>,
        substs: SubstsRef<'tcx>,
    ) -> Vec<(LocalDefId, SubstsRef<'tcx>)> {
        match &self.specification.posts {
            typed::SpecificationItem::Empty => vec![],
            typed::SpecificationItem::Inherent(posts)
            | typed::SpecificationItem::Refined(_, posts) => posts
                .iter()
                .map(|inherent_def_id| (*inherent_def_id, substs))
                .collect(),
            typed::SpecificationItem::Inherited(posts) => posts
                .iter()
                .map(|inherited_def_id| {
                    (
                        *inherited_def_id,
                        // Same comment as `functional_precondition` applies.
                        env.find_trait_method_substs(self.def_id, substs).unwrap().1,
                    )
                })
                .collect(),
        }
    }

    pub fn pledges(&self) -> impl Iterator<Item = &typed::Pledge> + '_ {
        self.specification
            .pledges
            .extract_with_selective_replacement_iter()
    }
}

/// Procedure contract as it is defined in MIR.
pub type ProcedureContractMirDef<'tcx> = ProcedureContractGeneric<mir::Local, mir::Place<'tcx>>;

/// Specialized procedure contract for use in translation.
pub type ProcedureContract<'tcx> = ProcedureContractGeneric<places::Local, places::Place<'tcx>>;

impl<L: fmt::Debug, P: fmt::Debug> fmt::Display for ProcedureContractGeneric<L, P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "ProcedureContract {{")?;
        writeln!(f, "IN:")?;
        for path in self.args.iter() {
            writeln!(f, "  {:?}", path)?;
        }
        writeln!(f, "OUT:")?;
        for path in self.returned_refs.iter() {
            writeln!(f, "  {:?}", path)?;
        }
        writeln!(f, "MAGIC:")?;
        for borrow_info in self.borrow_infos.iter() {
            writeln!(f, "{}", borrow_info)?;
        }
        writeln!(f, "}}")
    }
}

fn get_place_root(place: mir::Place) -> mir::Local {
    // match place {
    //     &mir::Place::Local(local) => local,
    //     &mir::Place::Projection(ref projection) => get_place_root(&projection.base),
    //     _ => unimplemented!(),
    // }
    place.local
}

impl<'tcx> ProcedureContractMirDef<'tcx> {
    /// Specialize to the definition site contract.
    pub fn to_def_site_contract(&self) -> ProcedureContract<'tcx> {
        let borrow_infos = self
            .borrow_infos
            .iter()
            .map(|info| BorrowInfo {
                region: info.region,
                blocking_paths: info
                    .blocking_paths
                    .iter()
                    .map(|(p, m)| (p.into(), *m))
                    .collect(),
                blocked_paths: info
                    .blocked_paths
                    .iter()
                    .map(|(p, m)| (p.into(), *m))
                    .collect(),
            })
            .collect();
        ProcedureContract {
            def_id: self.def_id,
            args: self.args.iter().map(|&a| a.into()).collect(),
            returned_refs: self
                .returned_refs
                .iter()
                .map(|(r, m)| (r.into(), *m))
                .collect(),
            returned_value: self.returned_value.into(),
            borrow_infos,
            specification: self.specification.clone(),
        }
    }

    /// Specialize to the call site contract.
    pub fn to_call_site_contract(
        &self,
        args: &[places::Local],
        target: places::Local,
    ) -> ProcedureContract<'tcx> {
        assert_eq!(self.args.len(), args.len());
        let mut substitutions = FxHashMap::default();
        substitutions.insert(self.returned_value, target);
        for (from, to) in self.args.iter().zip(args) {
            substitutions.insert(*from, *to);
        }
        let substitute = |(place, mutability): &(_, Mutability)| {
            let root = get_place_root(*place);
            let substitute_place = places::Place::SubstitutedPlace {
                substituted_root: *substitutions.get(&root).unwrap(),
                place: *place,
            };
            (substitute_place, *mutability)
        };
        let borrow_infos = self
            .borrow_infos
            .iter()
            .map(|info| BorrowInfo {
                region: info.region,
                blocking_paths: info.blocking_paths.iter().map(&substitute).collect(),
                blocked_paths: info.blocked_paths.iter().map(&substitute).collect(),
            })
            .collect();
        let returned_refs = self.returned_refs.iter().map(&substitute).collect();
        ProcedureContract {
            def_id: self.def_id,
            args: args.to_vec(),
            returned_refs,
            returned_value: target,
            borrow_infos,
            specification: self.specification.clone(),
        }
    }
}
