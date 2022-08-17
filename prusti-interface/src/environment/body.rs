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

/// Store for all the `mir::Body` which we've taken out of the compiler
/// or imported from external crates, all of which are indexed by DefId
pub struct EnvBody<'tcx> {
    tcx: TyCtxt<'tcx>,

    local_impure_fns: RefCell<FxHashMap<LocalDefId, BodyWithBorrowckFacts<'tcx>>>,
    // Loop invariants or triggers
    local_closures: RefCell<FxHashMap<LocalDefId, MirBody<'tcx>>>,

    local_pure_fns: FxHashMap<LocalDefId, MirBody<'tcx>>,
    local_predicates: FxHashMap<LocalDefId, MirBody<'tcx>>,
    local_specs: FxHashMap<LocalDefId, MirBody<'tcx>>,

    extern_pure_fns: FxHashMap<DefId, MirBody<'tcx>>,
    extern_predicates: FxHashMap<DefId, MirBody<'tcx>>,
    extern_specs: FxHashMap<DefId, MirBody<'tcx>>,

    /// Copies of above MIR bodies with the given substs applied.
    monomorphised_bodies: RefCell<FxHashMap<(DefId, SubstsRef<'tcx>), MirBody<'tcx>>>,
}

impl<'tcx> EnvBody<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        EnvBody {
            tcx,
            local_impure_fns: RefCell::new(FxHashMap::default()),
            local_closures: RefCell::new(FxHashMap::default()),
            local_pure_fns: FxHashMap::default(),
            local_predicates: FxHashMap::default(),
            local_specs: FxHashMap::default(),
            extern_pure_fns: FxHashMap::default(),
            extern_predicates: FxHashMap::default(),
            extern_specs: FxHashMap::default(),
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

    fn load_impure_fn_body(&self, def_id: LocalDefId) -> MirBody<'tcx> {
        let mut impure = self.local_impure_fns.borrow_mut();
        impure.entry(def_id).or_insert_with(|| Self::raw_load_local_mir(self.tcx, def_id)).body.clone()
    }

    /// Get the MIR body of a local impure function, monomorphised
    /// with the given type substitutions.
    pub fn get_impure_fn_body(
        &self,
        def_id: LocalDefId,
        substs: SubstsRef<'tcx>,
    ) -> MirBody<'tcx> {
        if let Some(body) = self.get_monomorphised(def_id.to_def_id(), substs) {
            return body;
        }
        let body = self.load_impure_fn_body(def_id);
        self.set_monomorphised(def_id.to_def_id(), substs, body)
    }

    fn load_closure_body(&self, def_id: LocalDefId) -> MirBody<'tcx> {
        let mut closures = self.local_closures.borrow_mut();
        closures.entry(def_id).or_insert_with(|| Self::raw_load_local_mir(self.tcx, def_id).body).clone()
    }

    /// Get the MIR body of a local closure (e.g. loop invariant or trigger),
    /// monomorphised with the given type substitutions.
    pub fn get_closure_body(
        &self,
        def_id: LocalDefId,
        substs: SubstsRef<'tcx>,
    ) -> MirBody<'tcx> {
        if let Some(body) = self.get_monomorphised(def_id.to_def_id(), substs) {
            return body;
        }
        let body = self.load_closure_body(def_id);
        self.set_monomorphised(def_id.to_def_id(), substs, body)
    }

    // Helper fn for
    fn extract_body(
        def_id: DefId,
        local_maps: &[&FxHashMap<LocalDefId, MirBody<'tcx>>],
        extern_maps: &[&FxHashMap<DefId, MirBody<'tcx>>]
    ) -> MirBody<'tcx> {
        if let Some(def_id) = def_id.as_local() {
            let mut local_maps = local_maps.iter();
            let init = local_maps.next().unwrap().get(&def_id);
            local_maps.fold(init, |acc, map|
                acc.or_else(|| map.get(&def_id))
            ).unwrap_or_else(|| panic!("Local body of `{:?}` was not loaded!", def_id)).clone()
        } else {
            let mut extern_maps = extern_maps.iter();
            let init = extern_maps.next().unwrap().get(&def_id);
            extern_maps.fold(init, |acc, map|
                acc.or_else(|| map.get(&def_id))
            ).unwrap_or_else(|| panic!("External body of `{:?}` was not imported!", def_id)).clone()
        }
    }

    /// Get the MIR body of a local or external pure function,
    /// monomorphised with the given type substitutions.
    pub fn get_pure_fn_body(
        &self,
        def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> MirBody<'tcx> {
        if let Some(body) = self.get_monomorphised(def_id, substs) {
            return body;
        }
        let body = Self::extract_body(
            def_id,
            &[&self.local_pure_fns],
            &[&self.extern_pure_fns],
        );
        self.set_monomorphised(def_id, substs, body)
    }

    /// Get the MIR body of a local or external expression (e.g. any spec or predicate),
    /// monomorphised with the given type substitutions.
    pub fn get_expression_body(
        &self,
        def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> MirBody<'tcx> {
        if let Some(body) = self.get_monomorphised(def_id, substs) {
            return body;
        }
        let body = Self::extract_body(
            def_id,
            &[&self.local_specs, &self.local_predicates],
            &[&self.extern_specs, &self.extern_predicates]
        );
        self.set_monomorphised(def_id, substs, body)
    }

    /// Get the MIR body of a local or external spec (pres/posts/pledges/type-specs),
    /// monomorphised with the given type substitutions.
    pub fn get_spec_body(
        &self,
        def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> MirBody<'tcx> {
        if let Some(body) = self.get_monomorphised(def_id, substs) {
            return body;
        }
        let body = Self::extract_body(
            def_id,
            &[&self.local_specs],
            &[&self.extern_specs]
        );
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
    /// prior to requesting their bodies with `get_spec_body` or exporting with `CrossCrateBodies::from`!
    pub(crate) fn load_spec_body(&mut self, def_id: LocalDefId) {
        Self::load_spec(self.tcx, &mut self.local_specs, def_id);
    }
    pub(crate) fn load_predicate_body(&mut self, def_id: LocalDefId) {
        Self::load_spec(self.tcx, &mut self.local_predicates, def_id);
    }
    fn load_spec(tcx: TyCtxt<'tcx>, map: &mut FxHashMap<LocalDefId, MirBody<'tcx>>, def_id: LocalDefId) {
        assert!(!map.contains_key(&def_id));
        map.insert(def_id, Self::raw_load_local_mir(tcx, def_id).body);
    }

    pub(crate) fn load_pure_fn_body(&mut self, def_id: LocalDefId) {
        assert!(!self.local_pure_fns.contains_key(&def_id));
        let body = Self::raw_load_local_mir(self.tcx, def_id);
        self.local_pure_fns.insert(def_id, body.body.clone());
        self.local_impure_fns.borrow_mut().insert(def_id, body);
    }

    /// Import non-local mir bodies of specs from cross-crate import.
    pub(crate) fn import_external_bodies(&mut self, bodies: CrossCrateBodies<'tcx>) {
        self.extern_pure_fns.extend(bodies.pure_fns);
        self.extern_predicates.extend(bodies.predicates);
        self.extern_specs.extend(bodies.specs);
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
            pure_fns: clone_map(&body.local_pure_fns),
            predicates: clone_map(&body.local_predicates),
            specs: clone_map(&body.local_specs),
        }
    }
}
