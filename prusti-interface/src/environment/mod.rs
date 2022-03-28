// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! This module defines the interface provided to a verifier.



use rustc_middle::mir;
use rustc_hir::hir_id::HirId;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::{self, TyCtxt};
use rustc_middle::ty::subst::SubstsRef;
use rustc_trait_selection::infer::{InferCtxtExt, TyCtxtInferExt};
use std::path::PathBuf;

use rustc_span::{MultiSpan, Span, symbol::Symbol};
use std::collections::HashSet;
use log::{debug, trace};
use std::rc::Rc;
use std::collections::HashMap;
use std::cell::RefCell;

pub mod borrowck;
mod collect_prusti_spec_visitor;
mod collect_closure_defs_visitor;
mod dump_borrowck_info;
mod loops;
mod loops_utils;
pub mod mir_analyses;
pub mod mir_storage;
pub mod mir_utils;
pub mod place_set;
pub mod polonius_info;
mod procedure;
pub mod mir_dump;
mod traits;

use self::collect_prusti_spec_visitor::CollectPrustiSpecVisitor;
use self::collect_closure_defs_visitor::CollectClosureDefsVisitor;
use rustc_hir::intravisit::Visitor;
pub use self::loops::{PlaceAccess, PlaceAccessKind, ProcedureLoops};
pub use self::loops_utils::*;
pub use self::procedure::{BasicBlockIndex, Procedure};
use self::borrowck::facts::BorrowckFacts;
// use config;
use crate::data::ProcedureDefId;
// use syntax::codemap::CodeMap;
// use syntax::codemap::Span;
// use utils::get_attr_value;
use rustc_span::source_map::SourceMap;

struct CachedBody<'tcx> {
    /// MIR body as known to the compiler.
    base_body: Rc<mir::Body<'tcx>>,
    /// Copies of the MIR body with the given substs applied.
    monomorphised_bodies: HashMap<SubstsRef<'tcx>, Rc<mir::Body<'tcx>>>,
    /// Cached borrowck information.
    borrowck_facts: Rc<BorrowckFacts>,
}

/// Facade to the Rust compiler.
// #[derive(Copy, Clone)]
pub struct Environment<'tcx> {
    /// Cached MIR bodies.
    bodies: RefCell<HashMap<LocalDefId, CachedBody<'tcx>>>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Environment<'tcx> {
    /// Builds an environment given a compiler state.
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Environment {
            tcx,
            bodies: RefCell::new(HashMap::new()),
        }
    }

    /// Returns the path of the source that is being compiled
    pub fn source_path(&self) -> PathBuf {
        self.tcx.sess.local_crate_source_file.clone().unwrap()
    }

    /// Returns the file name of the source that is being compiled
    pub fn source_file_name(&self) -> String {
        let source_path = self.source_path();
        source_path.file_name().unwrap().to_str().unwrap().to_owned()
    }

    /// Returns the name of the crate that is being compiled
    pub fn crate_name(&self) -> String {
        self.tcx
            .crate_name(rustc_span::def_id::LOCAL_CRATE)
            .to_string()
    }

    /// Returns the typing context
    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    /// Returns the type of a `HirId`
    pub fn hir_id_to_type(&self, hir_id: HirId) -> ty::Ty<'tcx> {
        let def_id = self.tcx.hir().local_def_id(hir_id);
        self.tcx.type_of(def_id)
    }

    /// Returns the `CodeMap`
    pub fn codemap(&self) -> &'tcx SourceMap {
        self.tcx.sess.source_map()
    }

    // /// Emits a warning message
    // pub fn warn(&self, msg: &str) {
    //     self.state.session.warn(msg);
    // }

    // /// Emits an warning message.
    // pub fn span_warn<S: Into<MultiSpan>>(&self, sp: S, msg: &str) {
    //     self.state.session.span_warn(sp, msg);
    // }

    // /// Emits an error message.
    // pub fn err(&self, msg: &str) {
    //     self.state.session.err(msg);
    // }

    // /// Emits an error message.
    // pub fn span_err<S: Into<MultiSpan>>(&self, sp: S, msg: &str) {
    //     self.state.session.span_err(sp, msg);
    // }

    /// Emits an error message.
    pub fn span_err_with_help_and_notes<S: Into<MultiSpan> + Clone>(
        &self,
        sp: S,
        msg: &str,
        help: &Option<String>,
        notes: &[(String, Option<S>)],
    ) {
        let mut diagnostic = self.tcx.sess.struct_err(msg);
        diagnostic.set_span(sp);
        if let Some(help_msg) = help {
            diagnostic.help(help_msg);
        }
        for (note_msg, opt_note_sp) in notes {
            if let Some(note_sp) = opt_note_sp {
                diagnostic.span_note(note_sp.clone(), note_msg);
            } else {
                diagnostic.note(note_msg);
            }
        }
        diagnostic.emit();
    }

    /// Emits an error message.
    pub fn span_warn_with_help_and_notes<S: Into<MultiSpan> + Clone>(
        &self,
        sp: S,
        msg: &str,
        help: &Option<String>,
        notes: &[(String, Option<S>)],
    ) {
        let mut diagnostic = self.tcx.sess.struct_warn(msg);
        diagnostic.set_span(sp);
        if let Some(help_msg) = help {
            diagnostic.help(help_msg);
        }
        for (note_msg, opt_note_sp) in notes {
            if let Some(note_sp) = opt_note_sp {
                diagnostic.span_note(note_sp.clone(), note_msg);
            } else {
                diagnostic.note(note_msg);
            }
        }
        diagnostic.emit();
    }

    /// Returns true if an error has been emitted
    pub fn has_errors(&self) -> bool {
        self.tcx.sess.has_errors()
    }

    /// Get ids of Rust procedures that are annotated with a Prusti specification
    pub fn get_annotated_procedures(&self) -> Vec<ProcedureDefId> {
        let tcx = self.tcx;
        let mut visitor = CollectPrustiSpecVisitor::new(self);
        tcx.hir().visit_all_item_likes(&mut visitor);

        let mut cl_visitor = CollectClosureDefsVisitor::new(self);
        tcx.hir().visit_all_item_likes(&mut cl_visitor.as_deep_visitor());

        let mut result: Vec<_> = visitor.get_annotated_procedures();
        result.extend(cl_visitor.get_closure_defs());
        result
    }

    /// Find whether the procedure has a particular `prusti::<name>` attribute.
    pub fn has_prusti_attribute(&self, def_id: ProcedureDefId, name: &str) -> bool {
        let tcx = self.tcx();
        crate::utils::has_prusti_attr(tcx.get_attrs(def_id), name)
    }

    /// Dump various information from the borrow checker.
    ///
    /// Mostly used for experiments and debugging.
    pub fn dump_borrowck_info(&self, procedures: &[ProcedureDefId]) {
        if prusti_common::config::dump_borrowck_info() {
            dump_borrowck_info::dump_borrowck_info(self, procedures)
        }
    }

    /// Get an absolute `def_path`. Note: not preserved across compilations!
    pub fn get_item_def_path(&self, def_id: DefId) -> String {
        let def_path = self.tcx.def_path(def_id);
        let mut crate_name = self.tcx.crate_name(def_path.krate).to_string();
        crate_name.push_str(&def_path.to_string_no_crate_verbose());
        crate_name
    }

    /// Get descriptive name prepended with crate name to make it unique.
    pub fn get_unique_item_name(&self, def_id: DefId) -> String {
        let def_path = self.tcx.def_path(def_id);
        format!(
            "{}::{}",
            self.tcx.crate_name(def_path.krate),
            self.tcx.def_path_str(def_id)
        )
    }

    /// Get the span of the given definition.
    pub fn get_def_span(&self, def_id: DefId) -> Span {
        self.tcx.def_span(def_id)
    }

    pub fn get_absolute_item_name(&self, def_id: DefId) -> String {
        self.tcx.def_path_str(def_id)
    }

    pub fn get_item_name(&self, def_id: DefId) -> String {
        self.tcx.def_path_str(def_id)
        // self.tcx().item_path_str(def_id)
    }

    /// Get a Procedure.
    pub fn get_procedure(&self, proc_def_id: ProcedureDefId) -> Procedure<'tcx> {
        Procedure::new(self, proc_def_id)
    }

    /// Get the MIR body of a local procedure, monomorphised with the given
    /// type substitutions.
    pub fn local_mir(
        &self,
        def_id: LocalDefId,
        substs: SubstsRef<'tcx>,
    ) -> Rc<mir::Body<'tcx>> {
        let mut bodies = self.bodies.borrow_mut();
        let body = bodies.entry(def_id)
            .or_insert_with(|| {
                // SAFETY: This is safe because we are feeding in the same `tcx`
                // that was used to store the data.
                let body_with_facts = unsafe {
                    self::mir_storage::retrieve_mir_body(self.tcx, def_id)
                };
                let body = body_with_facts.body;
                let facts = BorrowckFacts {
                    input_facts: RefCell::new(Some(body_with_facts.input_facts)),
                    output_facts: body_with_facts.output_facts,
                    location_table: RefCell::new(Some(body_with_facts.location_table)),
                };

                CachedBody {
                    base_body: Rc::new(body),
                    monomorphised_bodies: HashMap::new(),
                    borrowck_facts: Rc::new(facts),
                }
            });
        body
            .monomorphised_bodies
            .entry(substs)
            .or_insert_with(|| {
                use crate::rustc_middle::ty::subst::Subst;
                body.base_body.clone().subst(self.tcx, substs)
            })
            .clone()
    }

    /// Get Polonius facts of a local procedure.
    pub fn local_mir_borrowck_facts(&self, def_id: LocalDefId) -> Rc<BorrowckFacts> {
        self.try_get_local_mir_borrowck_facts(def_id).unwrap()
    }

    pub fn try_get_local_mir_borrowck_facts(&self, def_id: LocalDefId) -> Option<Rc<BorrowckFacts>> {
        trace!("try_get_local_mir_borrowck_facts: {:?}", def_id);
        self.bodies.borrow()
            .get(&def_id)
            .map(|body| body.borrowck_facts.clone())
    }

    /// Get the MIR body of an external procedure.
    pub fn external_mir<'a>(&self, def_id: DefId) -> &'a mir::Body<'tcx> {
        self.tcx().optimized_mir(def_id)
    }

    /// Get all relevant trait declarations for some type.
    pub fn get_traits_decls_for_type(&self, ty: &ty::Ty<'tcx>) -> HashSet<DefId> {
        let mut res = HashSet::new();
        let traits = self.tcx().all_traits();
        for trait_id in traits {
            self.tcx().for_each_relevant_impl(trait_id, *ty, |impl_id| {
                if let Some(relevant_trait_id) = self.tcx().trait_id_of_impl(impl_id) {
                    res.insert(relevant_trait_id);
                }
            });
        }
        res
    }

    /// Get an associated item by name.
    pub fn get_assoc_item(&self, id: DefId, name: Symbol) -> Option<ty::AssocItem> {
        // FIXME: Probably we should use https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/struct.AssociatedItems.html#method.find_by_name_and_namespace
        // instead.
        self.tcx().associated_items(id).filter_by_name_unhygienic(name).next().cloned()
    }

    /// Returns true iff `def_id` is a trait method
    pub fn is_trait_method(&self, def_id: ProcedureDefId) -> bool {
        self.tcx.trait_of_item(def_id).is_some()
    }

    /// Returns true iff `def_id` is an implementation of a trait method
    pub fn is_trait_method_impl(&self, def_id: ProcedureDefId) -> bool {
        self.tcx.impl_of_method(def_id)
            .and_then(|impl_id| self.tcx.trait_id_of_impl(impl_id))
            .is_some()
    }

    /// Returns the `DefId` of the corresponding trait method, if any.
    /// This should not be used to resolve calls (where substs are known): use
    /// `find_trait_method_substs` instead!
    pub fn find_trait_method(
        &self,
        impl_def_id: ProcedureDefId, // what are we calling?
    ) -> Option<DefId> {
        self.tcx
            .impl_of_method(impl_def_id)
            .and_then(|impl_id| self.tcx.trait_id_of_impl(impl_id))
            .and_then(|trait_id| self.get_assoc_item(trait_id, self.tcx().item_name(impl_def_id)))
            .map(|assoc_item| assoc_item.def_id)
    }

    /// If the given `impl_method_def_id` is an implementation of a trait
    /// method, return the `DefId` of that trait method as well as an adapted
    /// version of the callsite `impl_method_substs` substitutions.
    pub fn find_trait_method_substs(
        &self,
        impl_method_def_id: ProcedureDefId, // what are we calling?
        impl_method_substs: SubstsRef<'tcx>, // what are the substs on the call?
    ) -> Option<(ProcedureDefId, SubstsRef<'tcx>)> {
        let impl_def_id = self.tcx.impl_of_method(impl_method_def_id)?;
        let trait_ref = self.tcx.impl_trait_ref(impl_def_id)?;

        // At this point, we know that the given method:
        // - belongs to an impl block and
        // - the impl block implements a trait.
        // For the `get_assoc_item` call, we therefore `unwrap`, as not finding
        // the associated item would be a (compiler) internal error.
        let trait_def_id = trait_ref.def_id;
        let trait_method_def_id = self.get_assoc_item(
            trait_def_id,
            self.tcx().item_name(impl_method_def_id),
        ).unwrap().def_id;

        // sanity check: have we been given the correct number of substs?
        let identity_impl_method = self.identity_substs(impl_method_def_id);
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
        // What we need is a substs suitable for a call to Trait::f, whic is in
        // this case `[Struct<B, C>, A, X, Y, Z]`. More generally, it is the
        // concatenation of the trait ref substs with the identity of the impl
        // method after skipping the identity of the impl.
        let impl_substs = self.identity_substs(impl_def_id);
        let trait_method_substs = self.tcx.mk_substs(trait_ref.substs.iter()
            .chain(impl_method_substs.iter().skip(impl_substs.len())));

        // sanity check: do we now have the correct number of substs?
        let identity_trait_method = self.identity_substs(trait_method_def_id);
        assert_eq!(trait_method_substs.len(), identity_trait_method.len());

        Some((trait_method_def_id, trait_method_substs))
    }

    /// Given some procedure `proc_def_id` which is called, this method returns the actual method which will be executed when `proc_def_id` is defined on a trait.
    /// Returns `None` if this method can not be found or the provided `proc_def_id` is no trait item.
    pub fn find_impl_of_trait_method_call(&self, proc_def_id: ProcedureDefId, substs: SubstsRef<'tcx>) -> Option<ProcedureDefId> {
        // TODO(tymap): remove this method?
        if let Some(trait_id) = self.tcx().trait_of_item(proc_def_id) {
            debug!("Fetching implementations of method '{:?}' defined in trait '{}' with substs '{:?}'", proc_def_id, self.tcx().def_path_str(trait_id), substs);

            // TODO(tymap): don't use reveal_all
            let param_env = ty::ParamEnv::reveal_all();
            let key = ty::ParamEnvAnd { param_env, value: (proc_def_id, substs) };
            let resolved_instance = traits::resolve_instance(self.tcx(), key);
            return match resolved_instance {
                Ok(method_impl_instance) => {
                    let impl_method_def_id = method_impl_instance.map(|instance| instance.def_id());
                    debug!("Resolved to-be called method: {:?}", impl_method_def_id);
                    impl_method_def_id
                },
                Err(err) => {
                    debug!("Error while resolving the to-be called method: {:?}", err);
                    None
                }
            };
        } else {
            None
        }
    }

    /// Given a call to `called_def_id` from within `caller_def_id`, returns
    /// the `DefId` that will actually be called if known (i.e. if a trait
    /// method call actually resolves to a concrete implementation), as well as
    /// the correct substitutions for that call. If a method is not resolved,
    /// returns the original `called_def_id` and `call_substs`.
    pub fn resolve_method_call(
        &self,
        caller_def_id: ProcedureDefId, // where are we calling from?
        called_def_id: ProcedureDefId, // what are we calling?
        call_substs: SubstsRef<'tcx>,
    ) -> (ProcedureDefId, SubstsRef<'tcx>) {
        use crate::rustc_middle::ty::TypeFoldable;

        // avoids a compiler-internal panic
        if call_substs.needs_infer() {
            return (called_def_id, call_substs);
        }

        let param_env = self.tcx.param_env(caller_def_id);
        let instance = self.tcx
            .resolve_instance(param_env.and((called_def_id, call_substs)))
            .unwrap();
        if let Some(instance) = instance {
            (instance.def_id(), instance.substs)
        } else {
            (called_def_id, call_substs)
        }
    }

    pub fn type_is_allowed_in_pure_functions(&self, ty: ty::Ty<'tcx>, param_env: ty::ParamEnv<'tcx>) -> bool {
        match ty.kind() {
            ty::TyKind::Never => {
                true
            }
            _ => {
                self.type_is_copy(ty, param_env)
            }
        }
    }

    pub fn type_is_copy(&self, ty: ty::Ty<'tcx>, param_env: ty::ParamEnv<'tcx>) -> bool {
        let copy_trait = self.tcx.lang_items().copy_trait();
        if let Some(copy_trait_def_id) = copy_trait {
            // We need this check because `type_implements_trait`
            // panics when called on reference types.
            if let ty::TyKind::Ref(_, _, mutability) = ty.kind() {
                // Shared references are copy, mutable references are not.
                matches!(mutability, mir::Mutability::Not)
            } else {
                self.type_implements_trait(ty, copy_trait_def_id, param_env)
            }
        } else {
            false
        }
    }

    /// Checks whether the given type implements the trait with the given DefId.
    pub fn type_implements_trait(&self, ty: ty::Ty<'tcx>, trait_def_id: DefId, param_env: ty::ParamEnv<'tcx>) -> bool {
        assert!(self.tcx.is_trait(trait_def_id));
        self.tcx.infer_ctxt().enter(|infcx|
            infcx
                .type_implements_trait(trait_def_id, ty, ty::List::empty(), param_env)
                .must_apply_considering_regions()
        )
    }

    /// Return the default substitutions for a particular item, i.e. where each
    /// generic maps to itself.
    pub fn identity_substs(&self, def_id: ProcedureDefId) -> SubstsRef<'tcx> {
        ty::List::identity_for_item(self.tcx, def_id)
    }
}
