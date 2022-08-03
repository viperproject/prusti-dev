// This file was taken from the compiler:
// https://raw.githubusercontent.com/rust-lang/rust/03d488b48af9f66b91e9400387f781b82411fa82/compiler/rustc_trait_selection/src/traits/codegen.rs
// This file is licensed under Apache 2.0
// (https://github.com/rust-lang/rust/blob/03d488b48af9f66b91e9400387f781b82411fa82/LICENSE-APACHE)
// and MIT
// (https://github.com/rust-lang/rust/blob/03d488b48af9f66b91e9400387f781b82411fa82/LICENSE-MIT).

// Changes:
// + Fix compilation errors.
// + Remove all diagnostics (this is the main motivation for duplication).
// + Remove all `instrument`ation.
// + Replace `crate::*` imports with `prusti_rustc_interface::*` imports.


// This file contains various trait resolution methods used by codegen.
// They all assume regions can be erased and monomorphic types.  It
// seems likely that they should eventually be merged into more
// general routines.

use log::debug;
use prusti_rustc_interface::trait_selection::infer::{TyCtxtInferExt};
use prusti_rustc_interface::trait_selection::traits::{
    FulfillmentContext, ImplSource, Obligation, ObligationCause, SelectionContext, TraitEngine,
    Unimplemented,
};
use prusti_rustc_interface::middle::traits::CodegenObligationError;
use prusti_rustc_interface::middle::ty::{self, TyCtxt};

/// Attempts to resolve an obligation to an `ImplSource`. The result is
/// a shallow `ImplSource` resolution, meaning that we do not
/// (necessarily) resolve all nested obligations on the impl. Note
/// that type check should guarantee to us that all nested
/// obligations *could be* resolved if we wanted to.
///
/// This also expects that `trait_ref` is fully normalized.
pub(super) fn codegen_fulfill_obligation<'tcx>(
    tcx: TyCtxt<'tcx>,
    (param_env, trait_ref): (ty::ParamEnv<'tcx>, ty::PolyTraitRef<'tcx>),
) -> Result<&'tcx ImplSource<'tcx, ()>, CodegenObligationError> {
    // Remove any references to regions; this helps improve caching.
    let trait_ref = tcx.erase_regions(trait_ref);
    // We expect the input to be fully normalized.
    debug_assert_eq!(trait_ref, tcx.normalize_erasing_regions(param_env, trait_ref));
    debug!(
        "codegen_fulfill_obligation(trait_ref={:?}, def_id={:?})",
        (param_env, trait_ref),
        trait_ref.def_id()
    );

    // Do the initial selection for the obligation. This yields the
    // shallow result we are looking for -- that is, what specific impl.
    tcx.infer_ctxt().enter(|infcx| {
        let mut selcx = SelectionContext::new(&infcx);

        let obligation_cause = ObligationCause::dummy();
        let obligation =
            Obligation::new(obligation_cause, param_env, trait_ref.to_poly_trait_predicate());

        let selection = match selcx.select(&obligation) {
            Ok(Some(selection)) => selection,
            Ok(None) => return Err(CodegenObligationError::Ambiguity),
            Err(Unimplemented) => return Err(CodegenObligationError::Unimplemented),
            Err(e) => {
                panic!("Encountered error `{:?}` selecting `{:?}` during codegen", e, trait_ref)
            }
        };

        debug!("fulfill_obligation: selection={:?}", selection);

        // Currently, we use a fulfillment context to completely resolve
        // all nested obligations. This is because they can inform the
        // inference of the impl's type parameters.
        let mut fulfill_cx = FulfillmentContext::new();
        let impl_source = selection.map(|predicate| {
            debug!("fulfill_obligation: register_predicate_obligation {:?}", predicate);
            fulfill_cx.register_predicate_obligation(&infcx, predicate);
        });

        // In principle, we only need to do this so long as `impl_source`
        // contains unbound type parameters. It could be a slight
        // optimization to stop iterating early.
        let errors = fulfill_cx.select_all_or_error(&infcx);
        if !errors.is_empty() {
            return Err(CodegenObligationError::FulfillmentError);
        }

        let impl_source = infcx.resolve_vars_if_possible(impl_source);
        let impl_source = infcx.tcx.erase_regions(impl_source);

        // Opaque types may have gotten their hidden types constrained, but we can ignore them safely
        // as they will get constrained elsewhere, too.
        let _opaque_types = infcx.inner.borrow_mut().opaque_type_storage.take_opaque_types();

        debug!("Cache miss: {trait_ref:?} => {impl_source:?}");
        Ok(&*tcx.arena.alloc(impl_source))
    })
}
