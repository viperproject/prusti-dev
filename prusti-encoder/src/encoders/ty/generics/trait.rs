use prusti_rustc_interface::{middle::ty, span::def_id::DefId};
use rustc_hash::FxHashMap;
use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies};
use vir::{FunctionIdn, vir_format_identifier};

use crate::encoders::ty::generics::{GParams, GenericParamsEnc};

pub struct TraitEnc;

#[derive(Debug, Clone)]
pub struct TraitEncOutputRef<'vir> {
    pub trait_name: &'vir str,
    pub assoc_types:
        FxHashMap<DefId, FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap), vir::TyVal>>,
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
        for dom in Self::all_outputs_local_no_errors(program) {
            program.add_domain(dom);
        }
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let tcx = vcx.tcx();
            let trait_params = GParams::from(*task_key);
            let trait_generics = deps.require_dep::<GenericParamsEnc>(trait_params)?;

            let trait_name = vcx.alloc_str(tcx.item_name(task_key).as_str());

            let mut dom_funcs = Vec::new();
            let mut assoc_types = FxHashMap::default();

            for item in tcx.associated_items(task_key).in_definition_order() {
                if !matches!(item.kind, ty::AssocKind::Type { .. }) {
                    continue;
                }

                let def_id = item.def_id;

                // item_generics also includes parameters of trait itself
                let item_params = GParams::from(def_id);
                let item_generics = deps.require_dep::<GenericParamsEnc>(item_params)?;
                let item_name = tcx.item_name(def_id);

                let type_func = FunctionIdn::new(
                    vir_format_identifier!(vcx, "{trait_name}_assoc_type_{item_name}"),
                    (item_generics.ty_args(), item_generics.const_args()),
                    vir::TYPE_TYVAL,
                );
                assoc_types.insert(def_id, type_func);
                dom_funcs.push(vcx.mk_domain_function(type_func, false, None));
            }

            let impl_fun = FunctionIdn::new(
                vir_format_identifier!(vcx, "impl_{trait_name}"),
                (trait_generics.ty_args(), trait_generics.const_args()),
                vir::TYPE_BOOL,
            );
            deps.emit_output_ref(
                *task_key,
                TraitEncOutputRef {
                    trait_name,
                    assoc_types,
                    impl_fun,
                },
            )?;

            dom_funcs.push(vcx.mk_domain_function(impl_fun, false, None));

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
