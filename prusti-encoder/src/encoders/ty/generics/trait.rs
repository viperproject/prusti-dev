use prusti_rustc_interface::{middle::ty, span::def_id::DefId};
use rustc_hash::FxHashMap;
use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies};
use vir::{FunctionIdn, ViperIdent, vir_format_identifier};

use crate::encoders::{
    TyUsePureEnc,
    ty::{
        RustTyDecomposition,
        generics::{
            GParams, GenericParamsEnc,
            trait_impls::{self, TraitImplConditionEnc},
        },
        lifted::TyConstructorEnc,
    },
};

pub struct TraitEnc;

#[derive(Debug, Clone)]
pub struct TraitEncOutputRef<'vir> {
    pub trait_name: ViperIdent<'vir>,
    pub assoc_types:
        FxHashMap<DefId, FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap), vir::TyVal>>,
    pub assoc_consts:
        FxHashMap<DefId, FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap), vir::Snap>>,
    /// Whether the trait is implemented for the given trait arguments. Only
    /// ever stated positively (see [`TraitImplConditionEnc`]): nothing
    /// implies that a trait is *not* implemented, so an impl that is not part
    /// of the encoded program leaves implementedness open rather than false.
    pub impl_fun: FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap), vir::Bool>,
}

impl<'vir> OutputRefAny for TraitEncOutputRef<'vir> {}

impl TaskEncoder for TraitEnc {
    task_encoder::encoder_cache!(TraitEnc);
    const ENCODER_NAME: &'static str = "trait encoder";

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    type TaskDescription<'vir> = DefId;

    type OutputRef<'vir> = TraitEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = vir::Domain<'vir>;

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for domain in TraitEnc::all_outputs_local_no_errors(program) {
            program.add_domain(domain);
        }
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let tcx = vcx.tcx();
            let trait_params = Self::trait_params(*task_key);
            let trait_generics = deps.require_dep::<GenericParamsEnc>(trait_params)?;

            let trait_args = (trait_generics.ty_args(), trait_generics.const_args());

            let trait_name = ViperIdent::from_def_id(vcx, *task_key);

            let mut dom_funcs = Vec::new();
            let mut assoc_types = FxHashMap::default();
            let mut assoc_consts = FxHashMap::default();

            for item in tcx.associated_items(task_key).in_definition_order() {
                let item_did = item.def_id;

                // item_generics also includes parameters of trait itself
                let item_params = GParams::from(item_did);
                let item_generics = deps.require_dep::<GenericParamsEnc>(item_params)?;
                let item_name = ViperIdent::from_def_id(vcx, item_did);

                let args = (item_generics.ty_args(), item_generics.const_args());
                match item.kind {
                    ty::AssocKind::Type { .. } => {
                        let idn =
                            vir_format_identifier!(vcx, "{trait_name}_assoc_type_{item_name}");
                        let fun = FunctionIdn::new(idn, args, vir::TYPE_TYVAL);
                        assoc_types.insert(item_did, fun);
                        dom_funcs.push(vcx.mk_domain_function(fun, false, None));
                    }
                    ty::AssocKind::Const { .. } => {
                        let rust_ty = tcx.type_of(item_did).skip_binder();
                        let ty = RustTyDecomposition::from_ty(rust_ty, item_did);
                        let ret_ty = deps.require_ref::<TyUsePureEnc>(ty).unwrap().snapshot;

                        let idn =
                            vir_format_identifier!(vcx, "{trait_name}_assoc_const_{item_name}");
                        let fun = FunctionIdn::new(idn, args, ret_ty);
                        assoc_consts.insert(item_did, fun);
                        dom_funcs.push(vcx.mk_domain_function(fun, false, None));
                    }
                    ty::AssocKind::Fn { .. } => {}
                }
            }

            let impl_fun = FunctionIdn::new(
                vir_format_identifier!(vcx, "{trait_name}_impl"),
                trait_args,
                vir::TYPE_BOOL,
            );
            dom_funcs.push(vcx.mk_domain_function(impl_fun, false, None));

            // Emit the impl function reference early, so that it can be used to encode caller
            // bounds without causing dependency cycles.
            deps.emit_output_ref(
                *task_key,
                TraitEncOutputRef {
                    trait_name,
                    assoc_types,
                    assoc_consts,
                    impl_fun,
                },
            )?;

            // Each relevant impl contributes an axiom stating where it makes
            // `impl_fun` hold (see `impl_unlock_keys` for the gating).
            for impl_did in trait_impls::implementing_impls(tcx, *task_key) {
                let keys = trait_impls::impl_unlock_keys(impl_did);
                let span = tcx.def_span(impl_did);
                TyConstructorEnc::on_all_requested(keys.clone(), move || {
                    let _ = TraitImplConditionEnc::encode(impl_did, false, span);
                });
                // The impl's associated types resolve through the trait's
                // type functions declared above, so they unlock together
                // with the condition (fn items instead unlock per called
                // function, from `TraitFnEnc`). Only final definitions are
                // assumed (see `final_leaf_def`); defaults provided by the
                // trait are not supported.
                for item in tcx.associated_items(*task_key).in_definition_order() {
                    if !matches!(item.kind, ty::AssocKind::Type { .. }) {
                        continue;
                    }
                    let Some(leaf) = trait_impls::final_leaf_def(tcx, impl_did, item.def_id) else {
                        continue;
                    };
                    if leaf.defining_node.is_from_trait() {
                        continue;
                    }
                    let item_did = leaf.item.def_id;
                    TyConstructorEnc::on_all_requested(keys.clone(), move || {
                        let _ = trait_impls::TraitImplItemEnc::encode(
                            (impl_did, item_did),
                            false,
                            span,
                        );
                    });
                }
            }
            let trait_domain = vcx.mk_domain(
                vir_format_identifier!(vcx, "trait_{trait_name}"),
                &[],
                &[],
                vcx.alloc_slice(&dom_funcs),
                None,
            );

            Ok((trait_domain, ()))
        })
    }
}

impl TraitEnc {
    pub(super) fn trait_params<'tcx>(trait_did: DefId) -> GParams<'tcx> {
        GParams::from(trait_did).with_suffix("trait")
    }
}
