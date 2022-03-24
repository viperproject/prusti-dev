use crate::{PrustiError, specs::typed::{Pledge, ProcedureSpecification, SpecificationObligationKind}, utils::has_trait_bounds_ghost_constraint};
use rustc_hash::FxHashMap;
use rustc_hir::def_id::{DefId, LocalDefId};

/// Required interface
pub trait Extension {
    fn attrs_of(&self, local_def_id: LocalDefId) -> &[rustc_ast::ast::Attribute];
    fn get_span(&self, def_id: DefId) -> rustc_span::Span;
}

/// Used for constructing a procedure contract after typechecking. The partitioner
/// will ensure that [SpecificationObligationKind]s are correctly handled.
pub struct ProcSpecPartitioner<Ext: Extension> {
    ext: Ext,

    /// A contract without obligations ([SpecificationObligation::None])
    base_contract: ProcedureSpecification,

    /// A partitioning obligations to contracts under this obligation
    partition: FxHashMap<SpecificationObligationKind, ProcedureSpecification>,

    /// The function which this contract holds for (for error reporting
    target_function_def_id: DefId,
}

impl<AttrsGetter: Extension> ProcSpecPartitioner<AttrsGetter> {
    pub fn new(ext: AttrsGetter, target_function_def_id: DefId) -> Self {
        ProcSpecPartitioner {
            target_function_def_id,
            ext,
            base_contract: ProcedureSpecification::empty(),
            partition: FxHashMap::default(),
        }
    }

    pub fn add_precondition(&mut self, pre: LocalDefId) {
        let obligation = self.get_obligation(pre);
        if obligation == SpecificationObligationKind::None {
            self.base_contract.pres.push(pre);
            self.partition.values_mut().for_each(|s| s.pres.push(pre));
        } else {
            self.get_partitioned_mut(obligation).pres.push(pre);
        }
    }

    pub fn add_postcondition(&mut self, post: LocalDefId) {
        let obligation = self.get_obligation(post);
        if obligation == SpecificationObligationKind::None {
            self.base_contract.posts.push(post);
            self.partition.values_mut().for_each(|s| s.posts.push(post));
        } else {
            self.get_partitioned_mut(obligation).posts.push(post);
        }
    }

    pub fn add_pledge(&mut self, pledge: Pledge) {
        self.base_contract.pledges.push(pledge.clone());
        self.partition
            .values_mut()
            .for_each(|s| s.pledges.push(pledge.clone()));
    }

    pub fn set_trusted(&mut self, trusted: bool) {
        self.base_contract.trusted.set(trusted);
        self.partition
            .values_mut()
            .for_each(|s| s.trusted.set(trusted));
    }

    pub fn set_pure(&mut self, pure: bool) {
        self.base_contract.pure.set(pure);
        self.partition.values_mut().for_each(|s| s.pure.set(pure));
    }

    pub fn set_predicate(&mut self, predicate_id: LocalDefId) {
        self.base_contract.predicate_body.set(predicate_id);
        self.partition
            .values_mut()
            .for_each(|s| s.predicate_body.set(predicate_id));
    }

    /// Build the procedure contract (possibly with obligations) after all pre-/postconditions, etc.
    /// are added. Note that currently it is not possible to have multiple different obligation kinds.
    /// # Panics
    /// When there are multiple different obligation kinds registered.
    pub fn make_contract<'tcx>(self) -> Result<ProcedureSpecification, PrustiError> {
        if self.partition.is_empty() {
            Ok(self.base_contract)
        } else if self.partition.len() == 1 {
            /*
               Note: We only partition by obligation "kind" and do not parse the actual contents ("semantics") of the obligation here.
               For example, one could define two trait bound obligations kinds with different bounds, which is not valid.
               This is not checked here, but later when evaluating the obligation.
            */
            let mut base_contract = self.base_contract;

            if !*base_contract.trusted.expect_inherent() {
                let span = self.ext.get_span(self.target_function_def_id);
                return Err(PrustiError::unsupported("Ghost constraints can only be used on trusted functions", rustc_span::MultiSpan::from_span(span)));
            }

            base_contract.obligations = self.partition;
            Ok(base_contract)
        } else {
            let span = self.ext.get_span(self.target_function_def_id);
            return Err(PrustiError::unsupported("Multiple different specification obligations found, which is currently not supported in Prusti", rustc_span::MultiSpan::from_span(span)))
        }
    }

    fn get_partitioned_mut(
        &mut self,
        obligation: SpecificationObligationKind,
    ) -> &mut ProcedureSpecification {
        self.partition
            .entry(obligation)
            .or_insert_with(|| self.base_contract.clone())
    }

    /// Note: First wins, we do currently support not multiple constraints
    fn get_obligation(&self, spec: LocalDefId) -> SpecificationObligationKind {
        let attrs = self.ext.attrs_of(spec);
        if has_trait_bounds_ghost_constraint(attrs) {
            return SpecificationObligationKind::ResolveGenericParamTraitBounds;
        }

        SpecificationObligationKind::None
    }
}
