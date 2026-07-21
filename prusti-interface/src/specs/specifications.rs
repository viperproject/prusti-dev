use rustc_hash::FxHashMap;

use super::typed::{
    DefSpecificationMap, LoopSpecification, ProcedureSpecification, PrustiAssertion,
    PrustiAssumption, PrustiRefutation, TypeSpecification,
};
use crate::{data::ProcedureDefId, specs::typed::Refinable};
use prusti_rustc_interface::{
    hir::def_id::DefId,
    middle::ty::{self, GenericArgsRef},
};

/// Defines the context for which we perform refinement.
/// It can be thought of as the variants of [SpecQuery] for which we can perform refinement.
#[derive(Debug)]
struct RefinementContext<'qry, 'tcx> {
    impl_query: &'qry SpecQuery<'tcx>,
    trait_query: SpecQuery<'tcx>,
}

impl<'qry, 'tcx> RefinementContext<'qry, 'tcx> {
    /// Tries to create a refinement context.
    /// Returns None if refinement is not needed
    fn try_from(tcx: ty::TyCtxt<'tcx>, query: &'qry SpecQuery<'tcx>) -> Option<Self> {
        match query {
            SpecQuery::FunctionCallEncoding(FunctionCallEncodingQuery {
                called_def_id: def_id,
                call_substs: substs,
                ..
            })
            | SpecQuery::FunctionDefEncoding(def_id, substs)
            | SpecQuery::GetProcKind(def_id, substs) => {
                let (trait_def_id, trait_substs) = find_trait_method_substs(tcx, *def_id, substs)?;
                let trait_query = query.adapt_to(trait_def_id, trait_substs);
                Some(RefinementContext {
                    impl_query: query,
                    trait_query,
                })
            }
            // All other queries do not need refinement
            _ => None,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct FunctionCallEncodingQuery<'tcx> {
    pub called_def_id: DefId,
    pub caller_def_id: DefId,
    pub call_substs: GenericArgsRef<'tcx>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum SpecQuery<'tcx> {
    FunctionDefEncoding(DefId, GenericArgsRef<'tcx>),
    FunctionCallEncoding(FunctionCallEncodingQuery<'tcx>),
    /// For determining the [ProcedureSpecificationKind] of a procedure, e.g.
    /// for a check whether the function is pure or impure
    GetProcKind(DefId, GenericArgsRef<'tcx>),
    FetchSpan(DefId),
}

impl<'tcx> SpecQuery<'tcx> {
    pub fn referred_def_id(&self) -> DefId {
        match self {
            SpecQuery::FunctionDefEncoding(def_id, _)
            | SpecQuery::FunctionCallEncoding(FunctionCallEncodingQuery {
                called_def_id: def_id,
                ..
            })
            | SpecQuery::GetProcKind(def_id, _)
            | SpecQuery::FetchSpan(def_id) => *def_id,
        }
    }

    pub fn adapt_to(&self, new_def_id: DefId, new_substs: GenericArgsRef<'tcx>) -> Self {
        use SpecQuery::*;
        match self {
            FunctionDefEncoding(_, _) => FunctionDefEncoding(new_def_id, new_substs),
            FunctionCallEncoding(FunctionCallEncodingQuery { caller_def_id, .. }) => {
                FunctionCallEncoding(FunctionCallEncodingQuery {
                    called_def_id: new_def_id,
                    caller_def_id: *caller_def_id,
                    call_substs: new_substs,
                })
            }
            GetProcKind(_, _) => GetProcKind(new_def_id, new_substs),
            FetchSpan(_) => FetchSpan(new_def_id),
        }
    }
}

pub struct Specifications<'tcx> {
    user_typed_specs: DefSpecificationMap,

    /// A refinement can be different based on the query.
    /// The query can resolve to different [ProcedureSpecification]s due to type-conditional spec refinements.
    /// Since Prusti does currently not support refinements of type-conditional spec refinements, we
    /// store different refined versions for different queries.
    refined_specs: FxHashMap<SpecQuery<'tcx>, ProcedureSpecification>,
}

impl<'tcx> Specifications<'tcx> {
    pub fn new(user_typed_specs: DefSpecificationMap) -> Self {
        Self {
            user_typed_specs,
            refined_specs: FxHashMap::default(),
        }
    }

    pub fn get_type_specs(&self) -> &DefSpecificationMap {
        &self.user_typed_specs
    }

    #[tracing::instrument(level = "trace", skip(self))]
    pub fn get_loop_spec(&self, def_id: &DefId) -> Option<&LoopSpecification> {
        self.user_typed_specs.get_loop_spec(def_id)
    }

    #[tracing::instrument(level = "trace", skip(self))]
    pub fn get_type_spec(&self, def_id: &DefId) -> Option<&TypeSpecification> {
        self.user_typed_specs.get_type_spec(def_id)
    }

    #[tracing::instrument(level = "trace", skip(self))]
    pub fn get_assertion(&self, def_id: &DefId) -> Option<&PrustiAssertion> {
        self.user_typed_specs.get_assertion(def_id)
    }

    #[tracing::instrument(level = "trace", skip(self))]
    pub fn get_assumption(&self, def_id: &DefId) -> Option<&PrustiAssumption> {
        self.user_typed_specs.get_assumption(def_id)
    }

    #[tracing::instrument(level = "trace", skip(self))]
    pub fn get_refutation(&self, def_id: &DefId) -> Option<&PrustiRefutation> {
        self.user_typed_specs.get_refutation(def_id)
    }

    pub fn get_and_refine_proc_spec<'a, 'env: 'a>(
        &'a mut self,
        tcx: ty::TyCtxt<'tcx>,
        query: SpecQuery<'tcx>,
    ) -> Option<&'a ProcedureSpecification> {
        if self.is_refined(&query) {
            return self.get_proc_spec(&query);
        }

        match RefinementContext::try_from(tcx, &query) {
            Some(context) => {
                let refined =
                    self.perform_proc_spec_refinement(context.impl_query, &context.trait_query);
                assert!(
                    refined.is_some(),
                    "Could not perform refinement for {query:?}"
                );
                refined
            }
            _ => self.get_proc_spec(&query),
        }
    }

    #[tracing::instrument(level = "debug", skip(self))]
    fn perform_proc_spec_refinement<'a>(
        &'a mut self,
        impl_query: &SpecQuery<'tcx>,
        trait_query: &SpecQuery<'tcx>,
    ) -> Option<&'a ProcedureSpecification> {
        let impl_spec = self
            .get_proc_spec(impl_query)
            .cloned()
            .unwrap_or_else(|| ProcedureSpecification::empty(impl_query.referred_def_id()));

        let trait_spec = self
            .get_proc_spec(trait_query)
            .cloned()
            .unwrap_or_else(|| ProcedureSpecification::empty(trait_query.referred_def_id()));
        let refined = impl_spec.refine(&trait_spec);

        self.refined_specs.insert(*impl_query, refined);
        self.get_proc_spec(impl_query)
    }

    fn get_proc_spec<'a>(&'a self, query: &SpecQuery<'tcx>) -> Option<&'a ProcedureSpecification> {
        self.refined_specs.get(query).or_else(|| {
            self.user_typed_specs
                .get_proc_spec(&query.referred_def_id())
                .map(|spec| &spec.base_spec)
        })
    }

    fn is_refined(&self, query: &SpecQuery<'tcx>) -> bool {
        self.refined_specs.contains_key(query)
    }
}

/// If the given `impl_method_def_id` is an implementation of a trait
/// method, return the `DefId` of that trait method as well as an adapted
/// version of the callsite `impl_method_substs` substitutions.
pub fn find_trait_method_substs<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    impl_method_def_id: ProcedureDefId, // what are we calling?
    impl_method_substs: GenericArgsRef<'tcx>, // what are the substs on the call?
) -> Option<(ProcedureDefId, GenericArgsRef<'tcx>)> {
    let impl_def_id = tcx.impl_of_assoc(impl_method_def_id)?;
    let trait_ref = tcx.impl_trait_ref(impl_def_id)?.skip_binder();

    // At this point, we know that the given method:
    // - belongs to an impl block and
    // - the impl block implements a trait.
    // For the `get_assoc_item` call, we therefore `unwrap`, as not finding
    // the associated item would be a (compiler) internal error.
    let trait_def_id = trait_ref.def_id;
    let trait_method_def_id = get_assoc_item(tcx, trait_def_id, impl_method_def_id)
        .unwrap()
        .def_id;

    // sanity check: have we been given the correct number of substs?
    let identity_impl_method = ty::List::identity_for_item(tcx, impl_method_def_id);
    assert_eq!(identity_impl_method.len(), impl_method_substs.len());

    // Given:
    // ```
    // trait Trait<Tp> {
    //     fn f<Tx, Ty, Tz>();
    // }
    // struct Struct<Ex, Ey> { ... }
    // impl<A, B, C> Trait<A> for Struct<B, C> {
    //     fn f<X, Y, Z>() { ... }
    // }
    // ```
    //
    // The various substs look like this:
    // - identity for Trait:           `[Self, Tp]`
    // - identity for Trait::f:        `[Self, Tp, Tx, Ty, Tz]`
    // - substs of the impl trait ref: `[Struct<B, C>, A]`
    // - identity for the impl:        `[A, B, C]`
    // - identity for Struct::f:       `[A, B, C, X, Y, Z]`
    //
    // What we need is a substs suitable for a call to Trait::f, which is in
    // this case `[Struct<B, C>, A, X, Y, Z]`. More generally, it is the
    // concatenation of the trait ref substs with the identity of the impl
    // method after skipping the identity of the impl.
    //
    // We also need to subst the prefix (`[Struct<B, C>, A]` in the example
    // above) with call substs, so that we get the trait's type parameters
    // more precisely.
    let call_trait_substs =
        ty::EarlyBinder::bind(trait_ref.args).instantiate(tcx, impl_method_substs);
    let impl_substs = ty::List::identity_for_item(tcx, impl_def_id);
    let trait_method_substs = tcx.mk_args_from_iter(
        call_trait_substs
            .iter()
            .chain(impl_method_substs.iter().skip(impl_substs.len())),
    );

    // sanity check: do we now have the correct number of substs?
    let identity_trait_method = ty::List::identity_for_item(tcx, trait_method_def_id);
    assert_eq!(trait_method_substs.len(), identity_trait_method.len());

    Some((trait_method_def_id, trait_method_substs))
}

pub fn get_assoc_item<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    trait_id: DefId,
    item_id: DefId,
) -> Option<ty::AssocItem> {
    // FIXME: Probably we should use https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/struct.AssociatedItems.html#method.find_by_name_and_namespace
    // instead.
    tcx.associated_items(trait_id)
        .filter_by_name_unhygienic(tcx.item_name(item_id))
        .next()
        .cloned()
}
