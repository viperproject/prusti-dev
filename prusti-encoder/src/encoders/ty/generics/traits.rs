use prusti_rustc_interface::{middle::ty::AssocKind, span::def_id::DefId};
use rustc_hash::FxHashMap;
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, Dyn, FunctionIdn, vir_format_identifier};

use crate::encoders::ty::generics::{GArgs, GArgsTyEnc, GParams, GenericParamsEnc};

pub struct TraitEnc;

#[derive(Debug, Clone)]
pub struct TraitData<'vir> {
    pub trait_name: &'vir str,
    pub type_did_fun_mapping: FxHashMap<DefId, FunctionIdn<'vir, vir::ManyTyVal, vir::TyVal>>,
    pub impl_fun: FunctionIdn<'vir, vir::ManyTyVal, vir::Bool>,
}

#[derive(Debug, Clone)]
pub struct TraitEncOutput<'vir> {
    trait_domain: vir::Domain<'vir>,
    impl_fun: vir::Function<'vir>,
    impl_fun_unknown: vir::Function<'vir>,
}

impl TaskEncoder for TraitEnc {
    task_encoder::encoder_cache!(TraitEnc);

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    type TaskDescription<'vir> = DefId;

    type OutputFullDependency<'vir> = TraitData<'vir>;
    type OutputFullLocal<'vir> = TraitEncOutput<'vir>;

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for trait_enc in TraitEnc::all_outputs_local_no_errors() {
            program.add_domain(trait_enc.trait_domain);
            program.add_function(trait_enc.impl_fun);
            program.add_function(trait_enc.impl_fun_unknown);
        }
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        vir::with_vcx(|vcx| {
            let tcx = vcx.tcx();
            let params = deps.require_dep::<GenericParamsEnc>(GParams::from(*task_key))?;
            let trait_name = vcx.alloc_str(tcx.item_name(task_key).as_str());
            let type_did_fun_mapping = tcx
                .associated_items(task_key)
                .in_definition_order()
                .filter(|item| matches!(item.kind, AssocKind::Type { data: _ }))
                .map(|item| {
                    let params_type = deps
                        .require_dep::<GenericParamsEnc>(GParams::from(item.def_id))
                        .unwrap();
                    (
                        item.def_id,
                        FunctionIdn::new(
                            vir_format_identifier!(
                                vcx,
                                "{trait_name}_Assoc_{}_func",
                                tcx.item_name(item.def_id),
                            ),
                            vcx.alloc_slice(&vec![vir::TYPE_TYVAL; params_type.ty_exprs().len()]), // params_type also includes parameters of trait itself
                            vir::TYPE_TYVAL,
                        ),
                    )
                })
                .collect::<FxHashMap<_, _>>();
            let funcs = type_did_fun_mapping
                .values()
                .map(|function_idn| vcx.mk_domain_function(*function_idn, false, None))
                .collect::<Vec<_>>();

            let impl_fun_idn = FunctionIdn::new(
                vir_format_identifier!(vcx, "{trait_name}_impl"),
                vcx.alloc_slice(&(vec![vir::TYPE_TYVAL; params.ty_exprs().len()])),
                vir::TYPE_BOOL,
            );

            let impl_fun_unknown_idn: FunctionIdn<'vir, (vir::ManyTyVal, vir::Int), vir::Bool> = {
                // Omit the Self type as it is known to be the "Unknown_type"
                let unknown_params = vec![vir::TYPE_TYVAL; params.ty_exprs().len() - 1];
                FunctionIdn::new(
                    vir_format_identifier!(vcx, "{trait_name}_impl_unknown"),
                    (vcx.alloc_slice(&unknown_params), vir::TYPE_INT),
                    vir::TYPE_BOOL,
                )
            };
            let impl_fun_unknown = vcx.mk_function(
                impl_fun_unknown_idn,
                (
                    vcx.alloc_slice(&params.ty_decls()[1..]),
                    vcx.mk_local_decl("non_unit", vir::TYPE_INT),
                ),
                &[],
                &[],
                None,
                None,
            );

            let impl_fun_body = {
                let mut trait_impl_checks = Vec::new();

                for impl_did in tcx.all_impls(*task_key) {
                    let impl_ctx = GParams::from(impl_did);
                    let impl_params = deps.require_dep::<GenericParamsEnc>(impl_ctx)?;

                    let impl_trait_ref =
                        tcx.impl_trait_ref(impl_did).unwrap().instantiate_identity();
                    let impl_args =
                        deps.require_dep::<GArgsTyEnc>(GArgs::new(impl_ctx, impl_trait_ref.args))?;

                    let mut conjuncts = Vec::new();

                    for (trait_ty_param, impl_arg_val) in
                        params.ty_exprs().iter().zip(impl_args.get_ty())
                    {
                        conjuncts.push(vcx.mk_eq_expr(*trait_ty_param, *impl_arg_val));
                    }

                    // TODO: Add checks for the trait bounds

                    // Create an "exists" for each generic of the impl block
                    let trait_ty_decls = vcx.alloc_slice(
                        impl_params
                            .ty_decls()
                            .iter()
                            .map(|dec| dec.upcast_ty::<Dyn>())
                            .collect::<Vec<_>>()
                            .as_slice(),
                    );
                    let exists = vcx.mk_exists_expr(&trait_ty_decls, &[], vcx.mk_conj(&conjuncts));
                    trait_impl_checks.push(exists);
                }

                {
                    let non_unit_decl = vcx.mk_local_decl("non_unit", vir::TYPE_INT);
                    let non_unit_ex = vcx.mk_local_ex(non_unit_decl);
                    let unknown: FunctionIdn<'_, vir::Int, vir::TyVal> = FunctionIdn::new(
                        vir::vir_format_identifier!(vcx, "Unknown_type"),
                        vir::TYPE_INT,
                        vir::TYPE_TYVAL,
                    );
                    let self_is_unknown =
                        vcx.mk_eq_expr(params.ty_exprs()[0], unknown(non_unit_ex));

                    let unknown_impls = impl_fun_unknown_idn(&params.ty_exprs()[1..], non_unit_ex);

                    let exists_unknown = vcx.mk_exists_expr(
                        vcx.alloc_slice(&[non_unit_decl]),
                        &[],
                        vcx.mk_conj(&[self_is_unknown, unknown_impls]),
                    );

                    trait_impl_checks.push(exists_unknown);
                }

                vcx.mk_disj(&trait_impl_checks)
            };

            let impl_fun = vcx.mk_function(
                impl_fun_idn,
                (params.ty_decls(),),
                &[],
                &[],
                None,
                Some(impl_fun_body),
            );

            let trait_domain = vcx.mk_domain(
                vir_format_identifier!(vcx, "t_{trait_name}"),
                &[],
                &[],
                vcx.alloc_slice(funcs.as_slice()),
                None,
            );
            Ok((
                TraitEncOutput {
                    trait_domain,
                    impl_fun,
                    impl_fun_unknown,
                },
                TraitData {
                    trait_name,
                    type_did_fun_mapping,
                    impl_fun: impl_fun_idn,
                },
            ))
        })
    }
}
