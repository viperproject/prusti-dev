use prusti_rustc_interface::{middle::ty, span::def_id::DefId};
use rustc_hash::FxHashMap;
use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies};
use vir::{FunctionIdn, vir_format_identifier};

use crate::encoders::ty::{
    RustTyDecomposition,
    generics::{
        GParams, GenericParamsEnc, 
        builtin_trait::{SizedTraitEnc, TupleTraitEnc, BuiltinTraitEncTask},
        trait_impls::TraitImplEnc,
    },
    lifted::TyConstructorEnc,
    pure::TyPureEnc,
};

pub struct TraitEnc;

#[derive(Debug, Clone)]
pub struct TraitEncOutputRef<'vir> {
    pub trait_name: &'vir str,
    pub assoc_types:
        FxHashMap<DefId, FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap), vir::TyVal>>,
    pub assoc_consts:
        FxHashMap<DefId, FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap), vir::Snap>>,
    pub impl_fun: FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap), vir::Bool>,
    pub impl_for_unknown_fun:
        FunctionIdn<'vir, (vir::Int, vir::ManyTyVal, vir::ManyCSnap), vir::Bool>,
}

#[derive(Debug, Clone)]
pub struct TraitEncOutput<'vir> {
    trait_domain: vir::Domain<'vir>,
    impl_fun: vir::Function<'vir>,
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
    type OutputFullLocal<'vir> = Option<TraitEncOutput<'vir>>;

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in TraitEnc::all_outputs_local_no_errors(program) {
            let Some(output) = output else { continue };
            program.add_domain(output.trait_domain);
            program.add_function(output.impl_fun);
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
            let trait_decls = (trait_generics.ty_decls(), trait_generics.const_decls());

            let trait_name = vcx.alloc_str(tcx.item_name(task_key).as_str());

            let mut dom_funcs = Vec::new();
            let mut assoc_types = FxHashMap::default();
            let mut assoc_consts = FxHashMap::default();

            let mk_identifier = |item_name, item_type| {
                vir_format_identifier!(vcx, "{trait_name}_assoc_{item_type}_{item_name}")
            };

            for item in tcx.associated_items(task_key).in_definition_order() {
                let assoc_did = item.def_id;
                let assoc_name = tcx.item_name(assoc_did);
                let params = deps
                    .require_dep::<GenericParamsEnc>(GParams::from(assoc_did))
                    .unwrap();
                let args = (params.ty_args(), params.const_args());
                match item.kind {
                    ty::AssocKind::Type { .. } => {
                        let fun = FunctionIdn::new(
                            mk_identifier(assoc_name, "type"),
                            args,
                            vir::TYPE_TYVAL,
                        );
                        assoc_types.insert(assoc_did, fun);
                        dom_funcs.push(vcx.mk_domain_function(fun, false, None));
                    }
                    ty::AssocKind::Const { .. } => {
                        let rust_ty = tcx.type_of(assoc_did).skip_binder();
                        let decomp = RustTyDecomposition::from_ty(rust_ty, assoc_did);
                        let ret_ty = (deps.require_ref::<TyPureEnc>(decomp.ty).unwrap().domain)();

                        let fun =
                            FunctionIdn::new(mk_identifier(assoc_name, "const"), args, ret_ty);
                        assoc_consts.insert(assoc_did, fun);
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
            let impl_for_unknown_fun = {
                // Omit the `Self` type as it is known to be the unknown type
                let ty_args = &trait_args.0[1..];
                let const_args = trait_args.1;
                FunctionIdn::new(
                    vir_format_identifier!(vcx, "{trait_name}_impl_for_unknown"),
                    (vir::TYPE_INT, ty_args, const_args),
                    vir::TYPE_BOOL,
                )
            };

            // Emit the impl function reference early, so that it can be used to encode caller
            // bounds without causing dependency cycles.
            deps.emit_output_ref(
                *task_key,
                TraitEncOutputRef {
                    trait_name,
                    assoc_types,
                    assoc_consts,
                    impl_fun,
                    impl_for_unknown_fun,
                },
            )?;

            // When encoding builtin traits, emitting of the impl function is handled by
            // their respective builtin trait encoders. Activate them here.
            if tcx.lang_items().sized_trait() == Some(*task_key) {
                deps.require_dep::<SizedTraitEnc>(BuiltinTraitEncTask::Activate)?;
                return Ok((None, ()));
            }
            if tcx.lang_items().tuple_trait() == Some(*task_key) {
                deps.require_dep::<TupleTraitEnc>(BuiltinTraitEncTask::Activate)?;
                return Ok((None, ()));
            }

            let impl_fun_body = {
                let mut trait_impl_checks: Vec<_> = tcx
                    .all_impls(*task_key)
                    .map(|impl_did| {
                        deps.require_dep::<TraitImplEnc>(impl_did)
                            .unwrap()
                            .impl_condition
                    })
                    .collect();

                let unknown_type_check = {
                    let self_expr = trait_generics.ty_exprs()[0];

                    let is_unknown_type = vcx
                        .mk_adt_discriminator_expr(self_expr, TyConstructorEnc::UNKNOWN_TYPE_NAME);

                    let extracted_id =
                        TyConstructorEnc::unknown_type_id_accessor(vcx).call()(self_expr);

                    let unknown_impls = impl_for_unknown_fun(
                        extracted_id,
                        &trait_generics.ty_exprs()[1..],
                        trait_generics.const_exprs(),
                    );

                    vir::expr! { vcx;
                         (is_unknown_type) && (unknown_impls)
                    }
                };
                trait_impl_checks.push(unknown_type_check);

                vcx.mk_disj(&trait_impl_checks)
            };

            let ensures = vcx.mk_eq_expr(vcx.mk_result(vir::TYPE_BOOL), impl_fun_body);

            let impl_fun = vcx.mk_function(
                impl_fun,
                trait_decls,
                &[],
                vcx.alloc_slice(&[ensures]),
                Some(&vir::DecreasesGenData::Star),
                None,
            );

            let impl_for_unknown_fun = vcx.mk_domain_function(impl_for_unknown_fun, false, None);
            dom_funcs.push(impl_for_unknown_fun);

            let trait_domain = vcx.mk_domain(
                vir_format_identifier!(vcx, "trait_{trait_name}"),
                &[],
                &[],
                vcx.alloc_slice(&dom_funcs),
                None,
            );

            Ok((
                Some(TraitEncOutput {
                    trait_domain,
                    impl_fun,
                }),
                (),
            ))
        })
    }
}

impl TraitEnc {
    pub(super) fn trait_params<'tcx>(trait_did: DefId) -> GParams<'tcx> {
        GParams::from(trait_did).with_suffix("trait")
    }
}
