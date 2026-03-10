mod method;
mod function;
mod signature;

pub use function::*;
pub use method::*;
pub use signature::*;

use crate::encoders::ty::generics::{
    GArgs, GParams,
    r#trait::TraitEnc,
    trait_fn::{TraitFnEnc, TraitFnEncOutputRef},
    trait_impls::TraitImplEnc,
};

use prusti_interface::specs::specifications::SpecQuery;
use prusti_rustc_interface::{hir, middle::ty, span::def_id::DefId};
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CallTaskDescription<'tcx> {
    gargs: GArgs<'tcx>,
    callee: DefId,
    resolve_trait_calls: bool,
}

impl<'tcx> CallTaskDescription<'tcx> {
    pub fn new(
        context: impl Into<GParams<'tcx>>,
        args: &'tcx [ty::GenericArg<'tcx>],
        callee: DefId,
    ) -> Self {
        Self {
            gargs: GArgs::new(context, args),
            callee,
            resolve_trait_calls: true,
        }
    }

    pub fn resolve_trait_calls(self, resolve_trait_calls: bool) -> Self {
        Self {
            resolve_trait_calls,
            ..self
        }
    }

    fn trait_call<'vir, E: TaskEncoder>(
        &self,
        deps: &mut TaskEncoderDependencies<'vir, E>,
    ) -> Result<(DefId, Option<TraitFnEncOutputRef<'vir>>), EncodeFullError<'vir, E>> {
        let tcx = vir::with_vcx(|vcx| vcx.tcx());
        if self.resolve_trait_calls
            && let Some(assoc_item) = tcx.opt_associated_item(self.callee)
            && assoc_item.trait_container(tcx).is_some()
        {
            let assoc_enc = deps.require_ref::<TraitFnEnc>(assoc_item.def_id)?;
            Ok((assoc_item.def_id, Some(assoc_enc)))
        } else {
            Ok((self.callee, None))
        }
    }
}

// TODO: this should be a "crate" encoder, which will deps.require all the methods in the crate
pub fn encode_all_in_crate<'tcx>(tcx: ty::TyCtxt<'tcx>) {
    for def_id in tcx.hir_body_owners() {
        tracing::debug!("test_entrypoint item: {def_id:?}");
        match tcx.def_kind(def_id) {
            hir::def::DefKind::Fn | hir::def::DefKind::AssocFn => {
                let def_id = def_id.to_def_id();
                if prusti_interface::specs::is_spec_fn(tcx, def_id) {
                    continue;
                }

                let (is_pure, is_trusted) = crate::encoders::with_proc_spec(
                    SpecQuery::GetProcKind(def_id, ty::List::identity_for_item(tcx, def_id)),
                    |proc_spec| {
                        let is_pure = proc_spec.kind.is_pure().unwrap_or_default();
                        let is_trusted = proc_spec.trusted.extract_inherit().unwrap_or_default();
                        (is_pure, is_trusted)
                    },
                )
                .unwrap_or_default();

                if !(is_trusted && is_pure) {
                    let _ = method::MethodEnc::encode(def_id, false);
                }
            }
            unsupported_item_kind => {
                tracing::debug!("unsupported item: {unsupported_item_kind:?}");
            }
        }
    }

    // This creates the impl encoding for all traits in the crate
    // To iterate over all _visible_ impl blocks,
    // use tcx.visible_traits and tcx.all_impls(trait_id)
    for def_id in tcx.hir_crate_items(()).definitions() {
        match tcx.def_kind(def_id) {
            hir::def::DefKind::Trait => {
                TraitEnc::encode(def_id.to_def_id(), false).unwrap();
            }
            hir::def::DefKind::Impl { of_trait: true } => {
                TraitImplEnc::encode(def_id.to_def_id(), false).unwrap();
            }
            _ => (),
        }
    }
}
