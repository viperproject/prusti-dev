use prusti_rustc_interface::{
    middle::ty::{self, AssocKind},
    span::def_id::DefId,
};
use rustc_hash::FxHashMap;
use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies};
use vir::{CallableIdn, CastType, Dyn, FunctionIdn, vir_format_identifier};

use crate::encoders::ty::{
    RustTyDecomposition,
    generics::{GArgs, GArgsTyEnc, GParams, GenericParamsEnc},
    lifted::TyConstructorEnc,
};

pub struct TraitEnc;

#[derive(Debug, Clone)]
pub struct TraitData<'vir> {
    pub trait_name: &'vir str,
    pub type_did_fun_mapping: FxHashMap<DefId, FunctionIdn<'vir, vir::ManyTyVal, vir::TyVal>>,
    pub impl_fun: FunctionIdn<'vir, vir::ManyTyVal, vir::Bool>,
}

#[derive(Debug, Clone)]
pub struct TraitImplRef<'vir> {
    pub impl_fun: FunctionIdn<'vir, vir::ManyTyVal, vir::Bool>,
}
impl OutputRefAny for TraitImplRef<'_> {}

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
    type OutputRef<'vir> = TraitImplRef<'vir>;
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

            // Emit the impl function reference early, so that it can be used in the trait bounds
            // without causing dependency cycles.
            deps.emit_output_ref(
                *task_key,
                TraitImplRef {
                    impl_fun: impl_fun_idn,
                },
            )?;

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
                    // let impl_ctx = GParams::from(impl_did);
                    // let impl_params = deps.require_dep::<GenericParamsEnc>(impl_ctx)?;

                    // let impl_trait_ref =
                    //     tcx.impl_trait_ref(impl_did).unwrap().instantiate_identity();
                    // dbg!(&impl_trait_ref.args);

                    let implementing_ty = tcx.type_of(impl_did).instantiate_identity();

                    // Collect the locations of the generic parameters of the impl block from the
                    // `Self` type and the trait arguments. This will allos us to refer to them
                    // when encoding the trait bounds of the impl block.
                    let mut generics_map = HashMap::new();

                    let self_check_expr = encode_type(
                        vcx,
                        deps,
                        &mut generics_map,
                        impl_did,
                        params.ty_exprs()[0], // Self type
                        implementing_ty,
                    );

                    trait_impl_checks.push(self_check_expr);

                    // let impl_args =
                    //     deps.require_dep::<GArgsTyEnc>(GArgs::new(impl_ctx, impl_trait_ref.args))?;

                    // let mut conjuncts = Vec::new();
                    //
                    // for trait_pred in impl_ctx
                    //     .typing_env()
                    //     .param_env
                    //     .caller_bounds()
                    //     .iter()
                    //     .filter_map(ty::Clause::as_trait_clause)
                    //     .map(ty::Binder::skip_binder)
                    // {
                    //     let required_trait_impl_fun =
                    //         deps.require_ref::<Self>(trait_pred.def_id())?.impl_fun;
                    //     let predicate_args = deps.require_dep::<GArgsTyEnc>(GArgs::new(
                    //         impl_ctx,
                    //         trait_pred.trait_ref.args,
                    //     ))?;
                    //     conjuncts.push(required_trait_impl_fun(predicate_args.get_ty()));
                    // }

                    // Create an "exists" for each generic of the impl block
                    // let trait_ty_decls = vcx.alloc_slice(
                    //     impl_params
                    //         .ty_decls()
                    //         .iter()
                    //         .map(|dec| dec.upcast_ty::<Dyn>())
                    //         .collect::<Vec<_>>()
                    //         .as_slice(),
                    // );
                    // let exists = vcx.mk_exists_expr(trait_ty_decls, &[], vcx.mk_conj(&conjuncts));
                    // trait_impl_checks.push(exists);
                }

                {
                    // Add a case for unknown types that might implement the trait
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

fn encode_type<'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, TraitEnc>,
    generic_map: &mut HashMap<ty::GenericArg<'vir>, vir::ExprTyVal<'vir>>,
    def_id: DefId,
    base: vir::ExprTyVal<'vir>,
    ty: ty::Ty<'vir>,
) -> vir::ExprGenBool<'vir, (), !> {
    let decomp = RustTyDecomposition::from_ty(ty, def_id);

    if decomp.ty.specifics.is_param() {
        let generic_arg = decomp.args.args()[0];
        return if generic_map.contains_key(&generic_arg) {
            // If we have already seen this generic parameter, add an equality check to ensure it
            // is consistent with previous occurrences
            vcx.mk_eq_expr(base, generic_map[&decomp.args.args()[0]])
        } else {
            // If this is the first time we see this generic parameter, add it to the map and
            // continue encoding
            generic_map.insert(decomp.args.args()[0], base);
            vir::expr! {vcx; true}
        };
    }
    let ty_enc = deps.require_ref::<TyConstructorEnc>(decomp.ty).unwrap();

    let discr_check = vcx.mk_adt_discriminator_expr(base, ty_enc.ty_constructor.name().to_str());

    // Walk the type and recursively encode all inner types
    let inner_tys = decomp
        .args
        .args()
        .into_iter()
        .cloned()
        .filter_map(ty::GenericArg::as_type);

    let mut conjuncts = vec![discr_check];
    for (i, inner_ty) in inner_tys.into_iter().enumerate() {
        let new_base = ty_enc.ty_param_accessors[i].call()(base);
        let inner_ty_check = encode_type(vcx, deps, generic_map, def_id, new_base, inner_ty);
        conjuncts.push(inner_ty_check);
    }

    vcx.mk_conj(&conjuncts)
}
