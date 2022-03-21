use crate::{
    specs::typed::{
        Pledge, ProcedureSpecification, SpecificationObligationKind,
        WithPossibleObligation,
    },
    utils::has_trait_bounds_ghost_constraint,
};
use rustc_hash::FxHashMap;
use rustc_hir::def_id::LocalDefId;

/// Required interface
pub trait GetAttrs {
    fn attrs_of(&self, local_def_id: LocalDefId) -> &[rustc_ast::ast::Attribute];
}

/// Used for constructing a procedure contract after typechecking. The partitioner
/// will ensure that [SpecificationObligationKind]s are correctly handled.
pub struct ProcSpecPartitioner<AttrsGetter: GetAttrs> {
    get_attrs: AttrsGetter,

    /// A contract without obligations ([SpecificationObligation::None])
    base_contract: ProcedureSpecification,

    /// A partitioning of
    partition: FxHashMap<SpecificationObligationKind, ProcedureSpecification>,
}

impl<AttrsGetter: GetAttrs> ProcSpecPartitioner<AttrsGetter> {
    pub fn new(get_attrs: AttrsGetter) -> Self {
        ProcSpecPartitioner {
            get_attrs,
            base_contract: ProcedureSpecification::empty(),
            partition: FxHashMap::default(),
        }
    }

    pub fn add_precondition(&mut self, pre: LocalDefId) {
        let obligation = self.get_obligation(pre);
        if obligation == SpecificationObligationKind::None {
            self.base_contract.pres.push(pre);
        } else {
            self.get_partitioned_mut(obligation).pres.push(pre);
        }
    }

    pub fn add_postcondition(&mut self, post: LocalDefId) {
        let obligation = self.get_obligation(post);
        if obligation == SpecificationObligationKind::None {
            self.base_contract.posts.push(post);
        } else {
            self.get_partitioned_mut(obligation).posts.push(post);
        }
    }

    pub fn add_pledge(&mut self, pledge: Pledge) {
        self.base_contract.pledges.push(pledge);
    }

    pub fn set_trusted(&mut self, trusted: bool) {
        self.base_contract.trusted.set(trusted);
    }

    pub fn set_pure(&mut self, pure: bool) {
        self.base_contract.pure.set(pure);
    }

    pub fn set_predicate(&mut self, predicate_id: LocalDefId) {
        self.base_contract.predicate_body.set(predicate_id);
    }

    /// Build the procedure contract (possibly with obligations) after all pre-/postconditions, etc.
    /// are added. Note that currently it is not possible to have multiple different obligation kinds.
    /// # Panics
    /// When there are multiple different obligation kinds registered.
    pub fn make_contract(self) -> WithPossibleObligation<ProcedureSpecification> {
        if self.partition.is_empty() {
            WithPossibleObligation::WithoutObligation(self.base_contract)
        } else if self.partition.len() == 1 {
            /*
               Note: We only partition by obligation "kind" and do not parse the actual contents ("semantics") of the obligation here.
               For example, one could define two trait bound obligations kinds with different bounds, which is not valid.
               This is not checked here, but later when evaluating the obligation.
            */
            let (obligation, spec_under_obligation) = self.partition.into_iter().next().unwrap();
            WithPossibleObligation::WithObligation(
                obligation,
                spec_under_obligation,
                self.base_contract,
            )
        } else {
            // TODO hansenj: This should be a user error? Adjust method comment!
            panic!("Multiple different specification obligations found, which is currently not supported in Prusti")
        }
    }

    fn get_partitioned_mut(
        &mut self,
        obligation: SpecificationObligationKind,
    ) -> &mut ProcedureSpecification {
        self.partition
            .entry(obligation)
            .or_insert_with(ProcedureSpecification::empty)
    }

    /// Note: First wins, we do currently support not multiple constraints
    fn get_obligation(&self, spec: LocalDefId) -> SpecificationObligationKind {
        let attrs = self.get_attrs.attrs_of(spec);
        if has_trait_bounds_ghost_constraint(attrs) {
            return SpecificationObligationKind::ResolveGenericParamTraitBounds;
        }

        SpecificationObligationKind::None
    }
}
