use log::trace;
use prusti_rustc_interface::{
    macros::{TyDecodable, TyEncodable},
    middle::{
        mir,
        ty::{
            self,
            subst::{Subst, SubstsRef},
            TyCtxt,
        }
    },
    span::def_id::{DefId, LocalDefId},
};
use rustc_hash::FxHashMap;
use std::{cell::RefCell, rc::Rc, collections::hash_map::Entry};

use crate::environment::{
    mir_storage,
    borrowck::facts::BorrowckFacts,
};

/// Stores any possible MIR body (from the compiler) that
/// Prusti might want to work with. Cheap to clone
#[derive(Clone, TyEncodable, TyDecodable)]
pub struct MirBody<'tcx>(Rc<mir::Body<'tcx>>);
impl<'tcx> std::ops::Deref for MirBody<'tcx> {
    type Target = mir::Body<'tcx>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Stores body of functions which we'll need to encode as impure
struct BodyWithBorrowckFacts<'tcx> {
    body: MirBody<'tcx>,
    /// Cached borrowck information.
    borrowck_facts: Rc<BorrowckFacts>,
}

/// Bodies which need not be synched across crates and so can be
/// loaded dynamically as needed during encoding.
type DynamicallyLoadedBodies<T> = RefCell<FxHashMap<LocalDefId, T>>;
/// Bodies which must be exported across crates and thus must be
/// loaded prior to exporting (which happens before encoding).
struct PreLoadedBodies<'tcx> {
    local: FxHashMap<LocalDefId, MirBody<'tcx>>,
    external: FxHashMap<DefId, MirBody<'tcx>>,
}
impl<'tcx> PreLoadedBodies<'tcx> {
    fn new() -> Self {
        Self { local: Default::default(), external: Default::default() }
    }
    fn get(&self, def_id: DefId) -> Option<MirBody<'tcx>> {
        if let Some(def_id) = def_id.as_local() {
            self.local.get(&def_id).cloned()
        } else {
            self.external.get(&def_id).cloned()
        }
    }
    // For debugging use this rather than simply unwrap
    fn expect(&self, def_id: DefId) -> MirBody<'tcx> {
        let res = self.get(def_id);
        if let Some(def_id) = def_id.as_local() {
            res.unwrap_or_else(|| panic!("Local body of `{:?}` was not loaded!", def_id))
        } else {
            res.unwrap_or_else(|| panic!("External body of `{:?}` was not imported!", def_id))
        }
    }
}

/// Store for all the `mir::Body` which we've taken out of the compiler
/// or imported from external crates, all of which are indexed by DefId
pub struct EnvBody<'tcx> {
    tcx: TyCtxt<'tcx>,

    local_impure_fns: DynamicallyLoadedBodies<BodyWithBorrowckFacts<'tcx>>,
    // Loop invariants or triggers
    local_closures: DynamicallyLoadedBodies<MirBody<'tcx>>,

    pure_fns: PreLoadedBodies<'tcx>,
    predicates: PreLoadedBodies<'tcx>,
    specs: PreLoadedBodies<'tcx>,

    /// Copies of above MIR bodies with the given substs applied.
    monomorphised_bodies: RefCell<FxHashMap<(DefId, SubstsRef<'tcx>), MirBody<'tcx>>>,
}

impl<'tcx> EnvBody<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        EnvBody {
            tcx,
            local_impure_fns: RefCell::new(FxHashMap::default()),
            local_closures: RefCell::new(FxHashMap::default()),
            pure_fns: PreLoadedBodies::new(),
            predicates: PreLoadedBodies::new(),
            specs: PreLoadedBodies::new(),
            monomorphised_bodies: RefCell::new(FxHashMap::default()),
        }
    }

    // Common logic used internally by functions below to get local MIR bodies.
    fn raw_load_local_mir(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> BodyWithBorrowckFacts<'tcx> {
        // SAFETY: This is safe because we are feeding in the same `tcx`
        // that was used to store the data.
        let body_with_facts = unsafe { mir_storage::retrieve_mir_body(tcx, def_id) };

        let facts = BorrowckFacts {
            input_facts: RefCell::new(Some(body_with_facts.input_facts)),
            output_facts: body_with_facts.output_facts,
            location_table: RefCell::new(Some(body_with_facts.location_table)),
        };

        BodyWithBorrowckFacts {
            body: MirBody(Rc::new(body_with_facts.body)),
            borrowck_facts: Rc::new(facts),
        }
    }

    fn get_monomorphised(&self, def_id: DefId, substs: SubstsRef<'tcx>) -> Option<MirBody<'tcx>> {
        self.monomorphised_bodies.borrow().get(&(def_id, substs)).cloned()
    }
    fn set_monomorphised(
        &self,
        def_id: DefId,
        substs: SubstsRef<'tcx>,
        body: MirBody<'tcx>,
    ) -> MirBody<'tcx> {
        if let Entry::Vacant(v) =
                self.monomorphised_bodies.borrow_mut().entry((def_id, substs)) {
            v.insert(MirBody(ty::EarlyBinder(body.0).subst(self.tcx, substs))).clone()
        } else { unreachable!() }
    }

    /// Get the MIR body of a local impure function, without any substitutions.
    pub fn get_impure_fn_body(&self, def_id: LocalDefId) -> MirBody<'tcx> {
        let mut impure = self.local_impure_fns.borrow_mut();
        impure.entry(def_id).or_insert_with(|| Self::raw_load_local_mir(self.tcx, def_id)).body.clone()
    }

    /// Get the MIR body of a local impure function, monomorphised
    /// with the given type substitutions.
    pub fn get_impure_fn_body_subs(
        &self,
        def_id: LocalDefId,
        substs: SubstsRef<'tcx>,
    ) -> MirBody<'tcx> {
        if let Some(body) = self.get_monomorphised(def_id.to_def_id(), substs) {
            return body;
        }
        let body = self.get_impure_fn_body(def_id);
        self.set_monomorphised(def_id.to_def_id(), substs, body)
    }

    fn get_closure_body(&self, def_id: LocalDefId) -> MirBody<'tcx> {
        let mut closures = self.local_closures.borrow_mut();
        closures.entry(def_id).or_insert_with(|| Self::raw_load_local_mir(self.tcx, def_id).body).clone()
    }

    /// Get the MIR body of a local closure (e.g. loop invariant or trigger),
    /// monomorphised with the given type substitutions.
    pub fn get_closure_body_subs(
        &self,
        def_id: LocalDefId,
        substs: SubstsRef<'tcx>,
    ) -> MirBody<'tcx> {
        if let Some(body) = self.get_monomorphised(def_id.to_def_id(), substs) {
            return body;
        }
        let body = self.get_closure_body(def_id);
        self.set_monomorphised(def_id.to_def_id(), substs, body)
    }

    /// Get the MIR body of a local or external pure function,
    /// monomorphised with the given type substitutions.
    pub fn get_pure_fn_body_subs(
        &self,
        def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> MirBody<'tcx> {
        if let Some(body) = self.get_monomorphised(def_id, substs) {
            return body;
        }
        let body = self.pure_fns.expect(def_id);
        self.set_monomorphised(def_id, substs, body)
    }

    /// Get the MIR body of a local or external expression (e.g. any spec or predicate),
    /// monomorphised with the given type substitutions.
    pub fn get_expression_body_subs(
        &self,
        def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> MirBody<'tcx> {
        if let Some(body) = self.get_monomorphised(def_id, substs) {
            return body;
        }
        let body = self.specs.get(def_id).unwrap_or_else(||
            self.predicates.expect(def_id)
        );
        self.set_monomorphised(def_id, substs, body)
    }

    /// Get the MIR body of a local or external spec (pres/posts/pledges/type-specs),
    /// monomorphised with the given type substitutions.
    pub fn get_spec_body_subs(
        &self,
        def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> MirBody<'tcx> {
        if let Some(body) = self.get_monomorphised(def_id, substs) {
            return body;
        }
        let body = self.specs.expect(def_id);
        self.set_monomorphised(def_id, substs, body)
    }

    /// Get Polonius facts of a local procedure.
    pub fn local_mir_borrowck_facts(&self, def_id: LocalDefId) -> Rc<BorrowckFacts> {
        self.try_get_local_mir_borrowck_facts(def_id).unwrap()
    }

    pub fn try_get_local_mir_borrowck_facts(
        &self,
        def_id: LocalDefId,
    ) -> Option<Rc<BorrowckFacts>> {
        trace!("try_get_local_mir_borrowck_facts: {:?}", def_id);
        self
            .local_impure_fns
            .borrow()
            .get(&def_id)
            .map(|body| body.borrowck_facts.clone())
    }

    /// Ensures that the MIR body of a local spec is cached. This must be called on all specs,
    /// prior to requesting their bodies with `get_spec_body_subs` or exporting with `CrossCrateBodies::from`!
    pub(crate) fn load_spec_body(&mut self, def_id: LocalDefId) {
        // The same `def_id` may be referenced twice, e.g. see fn `constrained_contract_inherits_posts` in
        // the `ghost-constraints-extend-base-attributes.rs` test case
        if self.specs.local.contains_key(&def_id) { return; }
        self.specs.local.insert(def_id, Self::raw_load_local_mir(self.tcx, def_id).body);
    }
    pub(crate) fn load_predicate_body(&mut self, def_id: LocalDefId) {
        assert!(!self.predicates.local.contains_key(&def_id));
        self.predicates.local.insert(def_id, Self::raw_load_local_mir(self.tcx, def_id).body);
    }

    pub(crate) fn load_pure_fn_body(&mut self, def_id: LocalDefId) {
        assert!(!self.pure_fns.local.contains_key(&def_id));
        let bwbf = Self::raw_load_local_mir(self.tcx, def_id);
        self.pure_fns.local.insert(def_id, bwbf.body.clone());
        // Also add to `impure_fns` since we'll also be encoding this as impure
        self.local_impure_fns.borrow_mut().insert(def_id, bwbf);
    }

    /// Import non-local mir bodies of specs from cross-crate import.
    pub(crate) fn import_external_bodies(&mut self, bodies: CrossCrateBodies<'tcx>) {
        self.pure_fns.external.extend(bodies.pure_fns);
        self.predicates.external.extend(bodies.predicates);
        self.specs.external.extend(bodies.specs);
    }
}

#[derive(TyEncodable, TyDecodable)]
pub(crate) struct CrossCrateBodies<'tcx> {
    pure_fns: FxHashMap<DefId, MirBody<'tcx>>,
    predicates: FxHashMap<DefId, MirBody<'tcx>>,
    specs: FxHashMap<DefId, MirBody<'tcx>>,
}

impl<'tcx> From<&EnvBody<'tcx>> for CrossCrateBodies<'tcx> {
    fn from(body: &EnvBody<'tcx>) -> Self {
        let clone_map = |map: &FxHashMap<LocalDefId, MirBody<'tcx>>|
            map.iter().map(|(id, b)| (id.to_def_id(), b.clone())).collect();
        CrossCrateBodies {
            pure_fns: clone_map(&body.pure_fns.local),
            predicates: clone_map(&body.predicates.local),
            specs: clone_map(&body.specs.local),
        }
    }
}
