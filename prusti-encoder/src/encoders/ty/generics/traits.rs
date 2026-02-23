use prusti_rustc_interface::{middle::ty, span::def_id::DefId};
use rustc_hash::FxHashMap;
use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies};
use vir::{CallableIdn, CastType, FunctionIdn, vir_format_identifier};

use crate::encoders::{
    ConstEnc,
    r#const::ConstEncTask,
    ty::{
        RustTyDecomposition,
        generics::{GArgs, GArgsTyEnc, GParams, GenericParamsEnc},
        lifted::TyConstructorEnc,
        pure::TyPureEnc,
    },
};

pub struct TraitEnc;

type TraitArgs = (vir::ManyTyVal, vir::ManyCSnap);

#[derive(Debug, Clone)]
pub struct TraitEncOutputRef<'vir> {
    pub trait_name: &'vir str,
    pub assoc_types: FxHashMap<DefId, FunctionIdn<'vir, TraitArgs, vir::TyVal>>,
    pub assoc_consts: FxHashMap<DefId, FunctionIdn<'vir, TraitArgs, vir::Snap>>,
    pub impl_fun: FunctionIdn<'vir, TraitArgs, vir::Bool>,
}

#[derive(Debug, Clone)]
pub struct TraitImplRef<'vir> {
    pub assoc_types: FxHashMap<DefId, FunctionIdn<'vir, TraitArgs, vir::TyVal>>,
    pub assoc_consts: FxHashMap<DefId, FunctionIdn<'vir, TraitArgs, vir::Snap>>,
    pub impl_fun: FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap), vir::Bool>,
}
impl OutputRefAny for TraitEncOutputRef<'_> {}

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

    type OutputRef<'vir> = TraitEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = TraitEncOutput<'vir>;

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for trait_enc in TraitEnc::all_outputs_local_no_errors() {
            // Skip `Sized`, as we need a special encoding for its body. Encoded by `TyConstructorEnc`
            if trait_enc.trait_domain.name == "t_Sized" {
                continue;
            }
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
            let trait_items = tcx.associated_items(task_key);
            let assoc_types: FxHashMap<_, _> = trait_items
                .in_definition_order()
                .filter(|item| matches!(item.kind, ty::AssocKind::Type { .. }))
                .map(|ty| {
                    (
                        ty.def_id,
                        FunctionIdn::new(
                            vir_format_identifier!(vcx, "{trait_name}_Assoc_{}_func", ty.name(),),
                            (enc_params.ty_args(), enc_params.const_args()),
                            vir::TYPE_TYVAL,
                        ),
                    )
                })
                .collect();
            let assoc_consts: FxHashMap<_, _> = trait_items
                .in_definition_order()
                .filter(|item| matches!(item.kind, ty::AssocKind::Const { .. }))
                .map(|const_| {
                    let rust_ty = tcx.type_of(const_.def_id).skip_binder();
                    let decomp = RustTyDecomposition::from_ty(rust_ty, params);
                    let ret_ty = (deps.require_ref::<TyPureEnc>(decomp.ty).unwrap().domain)();
                    (
                        const_.def_id,
                        FunctionIdn::new(
                            vir_format_identifier!(
                                vcx,
                                "{trait_name}_Assoc_{}_func",
                                const_.name()
                            ),
                            (enc_params.ty_args(), enc_params.const_args()),
                            ret_ty,
                        ),
                    )
                })
                .collect();
            let funcs: Vec<_> = assoc_types
                .values()
                .map(|fun| vcx.mk_domain_function(*fun, false, None))
                .chain(
                    assoc_consts
                        .values()
                        .map(|fun| vcx.mk_domain_function(*fun, false, None)),
                )
                .collect();

            let impl_fun_idn = FunctionIdn::new(
                vir_format_identifier!(vcx, "{trait_name}_impl"),
                (enc_params.ty_args(), enc_params.const_args()),
                vir::TYPE_BOOL,
            );

            // Emit the impl function reference early, so that it can be used in the trait bounds
            // without causing dependency cycles.
            deps.emit_output_ref(
                *task_key,
                TraitEncOutputRef {
                    trait_name,
                    assoc_types,
                    assoc_consts,
                    impl_fun: impl_fun_idn,
                },
            )?;

            let impl_fun_unknown_idn: FunctionIdn<
                'vir,
                (vir::ManyTyVal, vir::ManyCSnap, vir::Int),
                vir::Bool,
            > = {
                // Omit the Self type as it is known to be the "Unknown_type"
                let unknown_args = &enc_params.ty_args()[1..];
                FunctionIdn::new(
                    vir_format_identifier!(vcx, "{trait_name}_impl_unknown"),
                    (unknown_args, enc_params.const_args(), vir::TYPE_INT),
                    vir::TYPE_BOOL,
                )
            };
            let impl_fun_unknown = vcx.mk_function(
                impl_fun_unknown_idn,
                (
                    &enc_params.ty_decls()[1..],
                    enc_params.const_decls(),
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
                    let mut ty_generics_map = FxHashMap::default();
                    let mut const_generics_map = FxHashMap::default();

                    let trait_ref = tcx.impl_trait_ref(impl_did).unwrap().instantiate_identity();
                    let rust_impl_args = trait_ref.args.iter().filter_map(|arg| arg.as_type());

                    let mut checks = Vec::new();
                    for (&ty_expr, rust_ty) in enc_params.ty_exprs().iter().zip(rust_impl_args) {
                        let check = encode_type_check(
                            vcx,
                            deps,
                            &mut ty_generics_map,
                            &mut const_generics_map,
                            impl_ctx,
                            ty_expr,
                            rust_ty,
                        );
                        checks.push(check);
                    }

                    let caller_bounds = impl_ctx.typing_env().param_env.caller_bounds();
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
                        let trait_args = trait_pred.trait_ref.args;
                        let ty_args = trait_args
                            .iter()
                            .filter_map(|arg| arg.as_type())
                            .map(|arg| {
                                assemble_type(
                                    tcx,
                                    deps,
                                    &ty_generics_map,
                                    &const_generics_map,
                                    impl_ctx,
                                    arg,
                                )
                            })
                            .collect::<Vec<_>>();

                        let const_args = trait_args
                            .iter()
                            .filter_map(|arg| arg.as_const())
                            .map(|const_| match const_.kind() {
                                ty::ConstKind::Param(..) => const_generics_map
                                    .get(&const_.into())
                                    .copied()
                                    .expect("The const generic should have been bound in the map")
                                    .downcast_ty(),
                                // TODO: we can figure out the type of the const value from the
                                // context, also make `ConstEnc` to handle unevaluated consts too
                                ty::ConstKind::Value(v) => {
                                    let task = ConstEncTask::Ty {
                                        const_,
                                        ty: v.ty,
                                        context: impl_ctx,
                                    };

                                    deps.require_dep::<ConstEnc>(task).unwrap()
                                }
                                _ => unimplemented!(
                                    "other kinds of const parameters not supported yet"
                                ),
                            })
                            .collect::<Vec<_>>();
                        checks.push(required_trait_impl_fun(&ty_args, &const_args));
                    }

                    for projection_pred in caller_bounds
                        .iter()
                        .filter_map(ty::Clause::as_projection_clause)
                        .map(ty::Binder::skip_binder)
                    {
                        let projection_did = projection_pred.def_id();
                        let required_trait_did = projection_pred.trait_def_id(tcx);
                        let required_trait = deps.require_ref::<Self>(required_trait_did)?;

                        let proj_src_args = projection_pred
                            .projection_term
                            .args
                            .iter()
                            .filter_map(|arg| arg.as_type());
                        let proj_src_ty_args = proj_src_args
                            .map(|ty| {
                                assemble_type(
                                    tcx,
                                    deps,
                                    &ty_generics_map,
                                    &const_generics_map,
                                    impl_ctx,
                                    ty,
                                )
                            })
                            .collect::<Vec<_>>();
                        let proj_src_const_args = projection_pred
                            .projection_term
                            .args
                            .iter()
                            .filter_map(|arg| arg.as_const())
                            .map(|const_| match const_.kind() {
                                ty::ConstKind::Param(..) => const_generics_map
                                    .get(&const_.into())
                                    .copied()
                                    .expect("The const generic should have been bound in the map")
                                    .downcast_ty(),
                                ty::ConstKind::Value(v) => {
                                    let task = ConstEncTask::Ty {
                                        const_,
                                        ty: v.ty,
                                        context: impl_ctx,
                                    };
                                    deps.require_dep::<ConstEnc>(task).unwrap()
                                }
                                _ => unimplemented!(
                                    "other kinds of const parameters not supported yet"
                                ),
                            })
                            .collect::<Vec<_>>();

                        match projection_pred.term.kind() {
                            ty::TermKind::Ty(tgt_ty) => {
                                let projection_fun = required_trait
                                    .assoc_types
                                    .get(&projection_did)
                                    .expect("Projection did should be in the mapping");

                                let tgt_ty_expr = assemble_type(
                                    tcx,
                                    deps,
                                    &ty_generics_map,
                                    &const_generics_map,
                                    impl_ctx,
                                    tgt_ty,
                                );
                                let projection =
                                    projection_fun(&proj_src_ty_args, &proj_src_const_args);
                                checks.push(vir::expr! {vcx; (projection) == (tgt_ty_expr)});
                            }
                            ty::TermKind::Const(const_) => {
                                let projection_fun = required_trait
                                    .assoc_consts
                                    .get(&projection_did)
                                    .expect("Projection did should be in the mapping");
                                let tgt_const_expr = match const_.kind() {
                                    ty::ConstKind::Param(..) => {
                                        const_generics_map.get(&const_.into()).copied().expect(
                                            "The const generic should have been bound in the map",
                                        )
                                    }
                                    ty::ConstKind::Value(val) => {
                                        let task = ConstEncTask::Ty {
                                            const_: const_,
                                            ty: val.ty,
                                            context: impl_ctx,
                                        };
                                        deps.require_dep::<ConstEnc>(task).unwrap().upcast_ty()
                                    }
                                    _ => unimplemented!(
                                        "other kinds of const parameters not supported yet"
                                    ),
                                };
                                let projection =
                                    projection_fun(&proj_src_ty_args, &proj_src_const_args);
                                checks.push(vir::expr! {vcx; (projection) == (tgt_const_expr) });
                            }
                        };
                    }

                    trait_impl_checks.push(vcx.mk_conj(&checks));
                }

                {
                    // Case for unknown types
                    let self_expr = enc_params.ty_exprs()[0];

                    let is_unknown_type = vcx.mk_adt_discriminator_expr(self_expr, "Unknown_type");

                    let unknown_id_destructor =
                        vcx.mk_adt_destructor("non_unit", vir::TYPE_TYVAL, vir::TYPE_INT);
                    let extracted_id = unknown_id_destructor.call()(self_expr);

                    let unknown_impls = impl_fun_unknown_idn(
                        &enc_params.ty_exprs()[1..],
                        enc_params.const_exprs(),
                        extracted_id,
                    );

                    let unknown_check = vcx.mk_conj(&[is_unknown_type, unknown_impls]);

                    trait_impl_checks.push(unknown_check);
                }

                vcx.mk_disj(&trait_impl_checks)
            };

            let impl_fun = vcx.mk_function(
                impl_fun_idn,
                (enc_params.ty_decls(), enc_params.const_decls()),
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
                (),
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
    ty_generics_map: &mut FxHashMap<ty::GenericArg<'vir>, vir::ExprTyVal<'vir>>,
    const_generics_map: &mut FxHashMap<ty::GenericArg<'vir>, vir::ExprSnap<'vir>>,
    ctx: GParams<'vir>,
    expr: vir::ExprTyVal<'vir>,
    ty: ty::Ty<'vir>,
) -> vir::ExprGenBool<'vir, (), !> {
    let decomp = RustTyDecomposition::from_ty(ty, ctx);

    if decomp.ty.specifics.is_param() {
        let arg = decomp.args.args().first().expect("Param missing arg");

        use std::collections::hash_map::Entry;
        return match ty_generics_map.entry(*arg) {
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

    let ty_enc = deps.require_ref::<TyConstructorEnc>(decomp.ty).unwrap();

    let discr_check = vcx.mk_adt_discriminator_expr(expr, ty_enc.ty_constructor.name().to_str());

    let mut conjuncts = vec![discr_check];

    let args = decomp.args.args();

    // Collect checks for inner types
    let inner_types = args.iter().filter_map(|arg| arg.as_type());
    for (i, inner_ty) in inner_types.enumerate() {
        let accessor = ty_enc.ty_param_accessors[i];

        let inner_expr = accessor.call()(expr);
        conjuncts.push(encode_type_check(
            vcx,
            deps,
            ty_generics_map,
            const_generics_map,
            ctx,
            inner_expr,
            inner_ty,
        ));
    }

    // Collect the "locations" of const parameters and assert equality for repeated occurances
    let consts = args.iter().filter_map(|arg| arg.as_const());
    for (i, const_) in consts.enumerate() {
        let accessor = ty_enc.const_param_accessors[i];
        let const_expr = accessor.call()(expr);

        match const_.kind() {
            ty::ConstKind::Param(..) => {
                use std::collections::hash_map::Entry;
                match const_generics_map.entry(const_.into()) {
                    Entry::Occupied(occ) => {
                        // Already seen this const parameter: ensure this const expression matches the originally found
                        conjuncts.push(vcx.mk_eq_expr(const_expr.upcast_ty(), *occ.get()));
                    }
                    Entry::Vacant(vac) => {
                        // First time seeing this const parameter: map it to the current accessor path for future references
                        vac.insert(const_expr.upcast_ty());
                    }
                }
            }
            ty::ConstKind::Value(val) => {
                let task = ConstEncTask::Ty {
                    const_,
                    ty: val.ty,
                    context: ctx,
                };
                let const_value = deps.require_dep::<ConstEnc>(task).unwrap();
                conjuncts.push(vcx.mk_eq_expr(const_expr, const_value));
            }
            _ => unimplemented!("other kinds of const parameters not supported yet"),
        }
    }

    vcx.mk_conj(&conjuncts)
}

/// Assemble a VIR type using the map of generic parameters we have collected earlier.
fn assemble_type<'vir>(
    tcx: ty::TyCtxt<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, TraitEnc>,
    ty_generics_map: &FxHashMap<ty::GenericArg<'vir>, vir::ExprTyVal<'vir>>,
    const_generics_map: &FxHashMap<ty::GenericArg<'vir>, vir::ExprSnap<'vir>>,
    ctx: GParams<'vir>,
    ty: ty::Ty<'vir>,
) -> vir::ExprTyVal<'vir> {
    let decomp = RustTyDecomposition::from_ty(ty, ctx);

    if decomp.ty.specifics.is_param() {
        let arg = decomp.args.args().first().expect("Param missing arg");
        return match arg.expect_ty().kind() {
            ty::TyKind::Param(param) => *ty_generics_map
                .get(arg)
                .expect(&format!("generic {param:?} to be mapped")),
            ty::TyKind::Alias(ty::AliasTyKind::Projection, alias) => {
                let trait_did = tcx.parent(alias.def_id);
                let trait_ = deps.require_ref::<TraitEnc>(trait_did).unwrap();

                let assoc_ty_fun = trait_
                    .assoc_types
                    .get(&alias.def_id)
                    .expect("associated type to be in the mapping");

                let gargs = GArgs::new(trait_did, alias.args);
                let gargs = deps.require_dep::<GArgsTyEnc>(gargs).unwrap();
                assoc_ty_fun(gargs.get_ty(), gargs.get_const())
            }
            _ => unimplemented!("unsupported kind of generic parameter in type position"),
        };
    }

    let ty_enc = deps.require_ref::<TyConstructorEnc>(decomp.ty).unwrap();

    let args = decomp.args.args();

    let inner_ty_args = args
        .iter()
        .filter_map(|arg| arg.as_type())
        .map(|inner_ty| {
            assemble_type(
                tcx,
                deps,
                ty_generics_map,
                const_generics_map,
                ctx,
                inner_ty,
            )
        })
        .collect::<Vec<_>>();

    let inner_const_args = args
        .iter()
        .filter_map(|arg| arg.as_const())
        .map(|const_| get_const_or_encode(deps, ctx, const_generics_map, const_).downcast_ty())
        .collect::<Vec<_>>();

    (ty_enc.ty_constructor)(&inner_ty_args, &inner_const_args)
}

fn get_const_or_encode<'vir>(
    deps: &mut TaskEncoderDependencies<'vir, TraitEnc>,
    ctx: GParams<'vir>,
    const_generics_map: &FxHashMap<ty::GenericArg<'vir>, vir::ExprSnap<'vir>>,
    const_: ty::Const<'vir>,
) -> vir::ExprSnap<'vir> {
    match const_.kind() {
        ty::ConstKind::Param(..) => const_generics_map
            .get(&const_.into())
            .copied()
            .expect("The const generic should have been bound in the map"),
        ty::ConstKind::Value(val) => {
            let task = ConstEncTask::Ty {
                const_: const_,
                ty: val.ty,
                context: ctx,
            };
            deps.require_dep::<ConstEnc>(task).unwrap().upcast_ty()
        }
        _ => unimplemented!("other kinds of const parameters not supported yet"),
    }
}
