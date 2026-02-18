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
            let params = GParams::from(*task_key);
            let enc_params = deps.require_dep::<GenericParamsEnc>(params)?;
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
                vcx.alloc_slice(&(vec![vir::TYPE_TYVAL; enc_params.ty_exprs().len()])),
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
                let unknown_params = vec![vir::TYPE_TYVAL; enc_params.ty_exprs().len() - 1];
                FunctionIdn::new(
                    vir_format_identifier!(vcx, "{trait_name}_impl_unknown"),
                    (vcx.alloc_slice(&unknown_params), vir::TYPE_INT),
                    vir::TYPE_BOOL,
                )
            };
            let impl_fun_unknown = vcx.mk_function(
                impl_fun_unknown_idn,
                (
                    vcx.alloc_slice(&enc_params.ty_decls()[1..]),
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

                    // Collect the locations of the generic parameters of the impl block from the
                    // `Self` type and the trait arguments. This will allos us to refer to them
                    // when encoding the trait bounds of the impl block.
                    let mut generics_map = HashMap::new();
                    let mut checks = Vec::new();

                    let trait_ref = tcx.impl_trait_ref(impl_did).unwrap().instantiate_identity();
                    let rust_impl_args = trait_ref.args.iter().filter_map(|arg| arg.as_type());

                    for (&ty_expr, rust_ty) in enc_params.ty_exprs().iter().zip(rust_impl_args) {
                        let check = encode_type_check(
                            vcx,
                            deps,
                            &mut generics_map,
                            impl_ctx,
                            ty_expr,
                            rust_ty,
                        );
                        checks.push(check);
                    }

                    // Construct the trait bound checks for this impl block
                    for trait_pred in impl_ctx
                        .typing_env()
                        .param_env
                        .caller_bounds()
                        .iter()
                        .filter_map(ty::Clause::as_trait_clause)
                        .map(ty::Binder::skip_binder)
                    {
                        let required_trait_impl_fun =
                            deps.require_ref::<Self>(trait_pred.def_id())?.impl_fun;
                        let args = trait_pred
                            .trait_ref
                            .args
                            .iter()
                            .map(|arg| {
                                generics_map.get(&arg).copied().unwrap_or_else(|| {
                                    todo!("Encode for non-generic arguments in trait bounds")
                                })
                            })
                            .collect::<Vec<_>>();
                        checks.push(required_trait_impl_fun(&args));
                    }

                    // let trait_bound_checks = vcx.mk_conj(&trait_bound_checks);

                    trait_impl_checks.push(vcx.mk_conj(&checks));
                    //     vcx.mk_bin_op_expr(vir::BinOpKind::And, self_ty_check, trait_bound_checks)
                    //         .downcast_ty(),
                    // );

                    // let impl_args =
                    //     deps.require_dep::<GArgsTyEnc>(GArgs::new(impl_ctx, impl_trait_ref.args))?;
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
                        vcx.mk_eq_expr(enc_params.ty_exprs()[0], unknown(non_unit_ex));

                    let unknown_impls =
                        impl_fun_unknown_idn(&enc_params.ty_exprs()[1..], non_unit_ex);

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
                (enc_params.ty_decls(),),
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

/// Encode a check that the type expression `expr` is the same as the rust type `ty`.
/// Additionally, collect the generic parameters of the impl block and map them to
/// their occurances in the type expression, such that they can be referred to when
/// encoding the trait bounds of the impl block.
///
/// For example, for `expr` equal to `(T, i32)`, `T` would be mapped to an accessor
/// expression to the first member of the tuple type - `expr.2_tup.0`
fn encode_type_check<'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, TraitEnc>,
    generic_map: &mut HashMap<ty::GenericArg<'vir>, vir::ExprTyVal<'vir>>,
    ctx: GParams<'vir>,
    expr: vir::ExprTyVal<'vir>,
    ty: ty::Ty<'vir>,
) -> vir::ExprGenBool<'vir, (), !> {
    let decomp = RustTyDecomposition::from_ty(ty, ctx);

    if decomp.ty.specifics.is_param() {
        let arg = decomp.args.args()[0];

        use std::collections::hash_map::Entry;
        return match generic_map.entry(arg) {
            Entry::Occupied(occ) => {
                // Already seen this T: ensure this type matches the originally found
                vcx.mk_eq_expr(expr, *occ.get())
            }
            Entry::Vacant(vac) => {
                // First time seeing T: map it to the current accessor path for future references
                vac.insert(expr);
                vir::expr! { vcx; true }
            }
        };
    }

    let ty_enc = deps
        .require_ref::<TyConstructorEnc>(decomp.ty)
        .expect("Type constructor encoder should have encoded this type");

    let discr_check = vcx.mk_adt_discriminator_expr(expr, ty_enc.ty_constructor.name().to_str());

    let mut conjuncts = vec![discr_check];

    // Collect checks for inner types
    let inner_types = decomp.args.args().iter().filter_map(|arg| arg.as_type());
    for (i, inner_ty) in inner_types.enumerate() {
        let accessor = ty_enc.ty_param_accessors[i];

        let inner_base = accessor.call()(expr);
        conjuncts.push(encode_type_check(
            vcx,
            deps,
            generic_map,
            ctx,
            inner_base,
            inner_ty,
        ));
    }

    vcx.mk_conj(&conjuncts)
}
