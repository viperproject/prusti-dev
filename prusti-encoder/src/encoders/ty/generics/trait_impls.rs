use rustc_hash::FxHashMap;
use std::collections::VecDeque;

use prusti_rustc_interface::{
    middle::{ty, ty::AssocKind},
    span::def_id::DefId,
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CallableIdn, CastType, Domain, vir_format_identifier};

use crate::encoders::{
    ConstEnc,
    r#const::ConstEncTask,
    ty::{
        RustTyDecomposition,
        generics::{GArgs, GArgsTyEnc, GParams, GenericParamsEnc, traits::TraitEnc},
        lifted::TyConstructorEnc,
    },
};

pub struct TraitImplEnc;

#[derive(Debug, Clone)]
pub struct TraitImplEncOutput<'vir> {
    pub impl_condition: vir::ExprBool<'vir>,
}

impl TaskEncoder for TraitImplEnc {
    task_encoder::encoder_cache!(TraitImplEnc);

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for dom in TraitImplEnc::all_outputs_local_no_errors() {
            program.add_domain(dom);
        }
    }

    type TaskDescription<'vir> = DefId;
    type OutputFullLocal<'vir> = Domain<'vir>;
    type OutputFullDependency<'vir> = TraitImplEncOutput<'vir>;

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;

        vir::with_vcx(|vcx| {
            let tcx = vcx.tcx();

            let impl_idx = {
                let all_impls = tcx.trait_impls_in_crate(task_key.krate);
                all_impls.iter().position(|did| did == task_key).unwrap()
            };

            let impl_ty = {
                let implementing_ty = tcx.type_of(task_key).instantiate_identity();
                let implementing_ty = RustTyDecomposition::from_ty(implementing_ty, *task_key);
                implementing_ty.ty.name()
            };

            let trait_ref = tcx.impl_trait_ref(task_key).unwrap().instantiate_identity();
            let trait_did = trait_ref.def_id;
            let trait_data = deps.require_ref::<TraitEnc>(trait_did)?;
            let trait_name = trait_data.trait_name;

            let ctx = GParams::from(*task_key);
            let params = deps.require_dep::<GenericParamsEnc>(ctx)?;
            let trait_ty_decls = params.ty_decls();
            let trait_const_decls = params.const_decls();
            let ty_cnt = params.ty_count();
            let const_cnt = params.const_count();

            let trait_args = deps.require_dep::<GArgsTyEnc>(GArgs::new(ctx, trait_ref.args))?;
            let trait_ty_args = trait_args.get_ty();
            let trait_const_args = trait_args.get_const();

            let mut axioms = Vec::new();
            for impl_item in tcx.associated_items(*task_key).in_definition_order() {
                let trait_item_did = impl_item.trait_item_def_id.unwrap();
                let item_did = impl_item.def_id;
                let item_name = tcx.item_name(item_did);

                // construct arguments for assoc_item function
                // parameters of the trait are substituted
                // by the arguments used in the impl
                // parameters of the associated type are kept

                // parameters of assoc item include already substituted arguments
                let item_ctx = GParams::from(item_did);
                let item_params = deps.require_dep::<GenericParamsEnc>(item_ctx).unwrap();

                let item_ty_decls = item_params.ty_decls();
                let item_const_decls = item_params.const_decls();
                let item_ty_args = item_params.ty_exprs();
                let item_const_args = item_params.const_exprs();

                // Combine substituted trait ty decls with the decls of the associated type
                let ty_decls = [&trait_ty_decls, &item_ty_decls[ty_cnt..]].concat();
                let const_decls = [&trait_const_decls, &item_const_decls[const_cnt..]].concat();

                // Combine substituted trait params with the params of the associated type
                let ty_args = &[trait_ty_args, &item_ty_args[ty_cnt..]].concat();
                let const_args = &[trait_const_args, &item_const_args[const_cnt..]].concat();

                match impl_item.kind {
                    AssocKind::Type { .. } => {
                        let assoc_type = trait_data.funs.assoc_types.get(&trait_item_did).unwrap();

                        // the type we want to resolve the type alias to
                        let assoc_type_expr = item_params.ty_expr(
                            deps,
                            RustTyDecomposition::from_ty(
                                tcx.type_of(item_did).instantiate_identity(),
                                item_ctx,
                            ),
                        );
                        axioms.push(vcx.mk_domain_axiom(
                            vir_format_identifier!(vcx, "{trait_name}_impl_{impl_ty}_{impl_idx}_assoc_type_{item_name}"),
                            vir::expr! {forall ..[ty_decls], ..[const_decls] :: {[assoc_type(ty_args, const_args)]} ([assoc_type(ty_args, const_args)]) == (assoc_type_expr)},
                        ));
                    }
                    _ => {
                        // unimplemented
                    }
                }
            }

            let domain = vcx.mk_domain(
                vir_format_identifier!(vcx, "t_{impl_idx}_{}_{impl_ty}", trait_data.trait_name,),
                &[],
                vcx.alloc_slice(&axioms),
                &[],
                None,
            );

            let impl_condition = impl_block_condition(vcx, deps, *task_key);

            Ok((domain, TraitImplEncOutput { impl_condition }))
        })
    }
}

fn impl_block_condition<'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, TraitImplEnc>,
    impl_did: DefId,
) -> vir::ExprBool<'vir> {
    let tcx = vcx.tcx();
    let impl_ctx = GParams::from(impl_did);

    let mut checks = Vec::new();

    // Collect the mappings from generic arguments to viper expressions that occur
    // in the impl block, such that we can refer to them when encoding the trait
    // bounds of the impl block. For example, for an impl like `impl<T> Trait for
    // (T, i32)`, we would map `T` to an accessor expression to the first member of
    // the tuple type - `self.2_tup.0`
    let mut ty_map = FxHashMap::default();
    let mut const_map = FxHashMap::default();

    let trait_ref = tcx.impl_trait_ref(impl_did).unwrap().instantiate_identity();
    let trait_rust_tys = trait_ref.args.iter().filter_map(|arg| arg.as_type());
    let trait_params = deps
        .require_dep::<GenericParamsEnc>(trait_ref.def_id.into())
        .unwrap();

    for (&ty_expr, rust_ty) in std::iter::zip(trait_params.ty_exprs(), trait_rust_tys) {
        checks.extend(encode_type_check(
            vcx,
            deps,
            &mut ty_map,
            &mut const_map,
            impl_ctx,
            ty_expr,
            rust_ty,
        ));
    }

    let caller_bounds = impl_ctx.typing_env().param_env.caller_bounds();

    // Process the projection predicates first as they might introduce new bindings
    // for generic parameters
    let projection_preds = caller_bounds
        .iter()
        .filter_map(ty::Clause::as_projection_clause)
        .map(ty::Binder::skip_binder);

    checks.extend(process_projection_predicates(
        vcx,
        deps,
        &mut ty_map,
        &mut const_map,
        impl_ctx,
        projection_preds,
    ));

    // Process trait predicates last as they cannot introduce new bindings for
    // generics
    let trait_preds = caller_bounds
        .iter()
        .filter_map(ty::Clause::as_trait_clause)
        .map(ty::Binder::skip_binder);

    checks.push(process_trait_predicates(
        vcx,
        deps,
        &ty_map,
        &const_map,
        impl_ctx,
        trait_preds,
    ));

    vcx.mk_conj(&checks)
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
    deps: &mut TaskEncoderDependencies<'vir, TraitImplEnc>,
    ty_map: &mut FxHashMap<ty::GenericArg<'vir>, vir::ExprTyVal<'vir>>,
    const_map: &mut FxHashMap<ty::GenericArg<'vir>, vir::ExprSnap<'vir>>,
    ctx: GParams<'vir>,
    expr: vir::ExprTyVal<'vir>,
    ty: ty::Ty<'vir>,
) -> Option<vir::ExprBool<'vir>> {
    let decomp = RustTyDecomposition::from_ty(ty, ctx);

    if decomp.ty.specifics.is_param() {
        let arg = decomp.args.args().first().expect("Param missing arg");

        use std::collections::hash_map::Entry;
        return match ty_map.entry(*arg) {
            Entry::Occupied(occ) => {
                // Already seen this T: ensure this type matches the originally found
                Some(vcx.mk_eq_expr(expr, *occ.get()))
            }
            Entry::Vacant(vac) => {
                // First time seeing T: map it to the current accessor path for future references
                vac.insert(expr);
                None
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

        let expr = accessor.call()(expr);
        conjuncts.extend(encode_type_check(
            vcx, deps, ty_map, const_map, ctx, expr, inner_ty,
        ));
    }

    // Collect the "locations" of const parameters and assert equality for repeated occurances
    let consts = args.iter().filter_map(|arg| arg.as_const());
    for (i, const_) in consts.enumerate() {
        let accessor = ty_enc.const_param_accessors[i];
        let expr = accessor.call()(expr);

        conjuncts.extend(encode_const_check(
            vcx,
            deps,
            const_map,
            ctx,
            expr.upcast_ty(),
            const_,
        ));
    }

    Some(vcx.mk_conj(&conjuncts))
}

/// Encode a check that the expression `expr` is the same as the rust const `const_`.
fn encode_const_check<'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, TraitImplEnc>,
    const_map: &mut FxHashMap<ty::GenericArg<'vir>, vir::ExprSnap<'vir>>,
    ctx: GParams<'vir>,
    expr: vir::ExprSnap<'vir>,
    const_: ty::Const<'vir>,
) -> Option<vir::ExprBool<'vir>> {
    match const_.kind() {
        ty::ConstKind::Param(..) => {
            use std::collections::hash_map::Entry;
            match const_map.entry(const_.into()) {
                Entry::Occupied(occ) => {
                    // Already seen this const parameter: ensure this const expression matches the originally found
                    Some(vcx.mk_eq_expr(expr, *occ.get()))
                }
                Entry::Vacant(vac) => {
                    // First time seeing this const parameter: map it to the current accessor path for future references
                    vac.insert(expr);
                    None
                }
            }
        }
        ty::ConstKind::Value(val) => {
            let task = ConstEncTask::Ty {
                const_,
                ty: val.ty,
                context: ctx,
            };
            let value = deps.require_dep::<ConstEnc>(task).unwrap();
            Some(vcx.mk_eq_expr(expr, value.upcast_ty()))
        }
        _ => unimplemented!("other kinds of const parameters not supported yet"),
    }
}

/// Assemble a VIR type using the map of generic parameters we have collected earlier.
fn assemble_type<'vir>(
    tcx: ty::TyCtxt<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, TraitImplEnc>,
    ty_map: &FxHashMap<ty::GenericArg<'vir>, vir::ExprTyVal<'vir>>,
    const_map: &FxHashMap<ty::GenericArg<'vir>, vir::ExprSnap<'vir>>,
    ctx: GParams<'vir>,
    ty: ty::Ty<'vir>,
) -> vir::ExprTyVal<'vir> {
    let decomp = RustTyDecomposition::from_ty(ty, ctx);

    if decomp.ty.specifics.is_param() {
        let arg = decomp.args.args().first().expect("Param missing arg");
        return match arg.expect_ty().kind() {
            ty::TyKind::Param(param) => *ty_map
                .get(arg)
                .expect(&format!("generic {param:?} to be mapped")),
            ty::TyKind::Alias(ty::AliasTyKind::Projection, alias) => {
                let trait_did = tcx.parent(alias.def_id);
                let trait_ = deps.require_ref::<TraitEnc>(trait_did).unwrap();

                let assoc_ty_fun = trait_
                    .funs
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
        .map(|inner_ty| assemble_type(tcx, deps, ty_map, const_map, ctx, inner_ty))
        .collect::<Vec<_>>();

    let inner_const_args = args
        .iter()
        .filter_map(|arg| arg.as_const())
        .map(|const_| assemble_const(deps, ctx, const_map, const_).downcast_ty())
        .collect::<Vec<_>>();

    (ty_enc.ty_constructor)(&inner_ty_args, &inner_const_args)
}

fn assemble_const<'vir>(
    deps: &mut TaskEncoderDependencies<'vir, TraitImplEnc>,
    ctx: GParams<'vir>,
    const_map: &FxHashMap<ty::GenericArg<'vir>, vir::ExprSnap<'vir>>,
    const_: ty::Const<'vir>,
) -> vir::ExprSnap<'vir> {
    match const_.kind() {
        ty::ConstKind::Param(..) => const_map
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

/// Process the projection predicates in a topological order, such that when processing a
/// projection predicate, the projection term is already mapped to a VIR expression. This is needed
/// to handle cases like `T::Item: Trait` where we need to refer to `T::Item` when encoding the
/// trait bound check for `Trait`.
fn process_projection_predicates<'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, TraitImplEnc>,
    ty_map: &mut FxHashMap<ty::GenericArg<'vir>, vir::ExprTyVal<'vir>>,
    const_map: &mut FxHashMap<ty::GenericArg<'vir>, vir::ExprSnap<'vir>>,
    ctx: GParams<'vir>,
    projections: impl Iterator<Item = ty::ProjectionPredicate<'vir>>,
) -> Option<vir::ExprBool<'vir>> {
    let mut worklist: VecDeque<_> = projections.collect();
    let mut conjuncts = Vec::new();
    while let Some(proj) = worklist.pop_front() {
        if is_alias_ready(&proj.projection_term, ty_map, const_map) {
            conjuncts.extend(process_projection(vcx, deps, ty_map, const_map, ctx, proj));
        } else {
            worklist.push_back(proj);
        }
    }
    if conjuncts.is_empty() {
        None
    } else {
        Some(vcx.mk_conj(&conjuncts))
    }
}

fn process_projection<'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, TraitImplEnc>,
    ty_map: &mut FxHashMap<ty::GenericArg<'vir>, vir::ExprTyVal<'vir>>,
    const_map: &mut FxHashMap<ty::GenericArg<'vir>, vir::ExprSnap<'vir>>,
    ctx: GParams<'vir>,
    projection: ty::ProjectionPredicate<'vir>,
) -> Option<vir::ExprBool<'vir>> {
    let tcx = vcx.tcx();
    let proj_did = projection.def_id();
    let trait_did = projection.trait_def_id(tcx);
    let trait_ = deps.require_ref::<TraitEnc>(trait_did).unwrap();

    let proj_args = projection.projection_term.args;

    let proj_ty_args: Vec<_> = proj_args
        .iter()
        .filter_map(|arg| arg.as_type())
        .map(|ty| assemble_type(tcx, deps, ty_map, const_map, ctx, ty))
        .collect();
    let proj_const_args: Vec<_> = proj_args
        .iter()
        .filter_map(|arg| arg.as_const())
        .map(|const_| assemble_const(deps, ctx, const_map, const_).downcast_ty())
        .collect();

    match projection.term.kind() {
        ty::TermKind::Ty(tgt_ty) => {
            let projection_fun = trait_
                .funs
                .assoc_types
                .get(&proj_did)
                .expect("Projection did should be in the mapping");

            let projection = projection_fun(&proj_ty_args, &proj_const_args);

            encode_type_check(vcx, deps, ty_map, const_map, ctx, projection, tgt_ty)
        }
        ty::TermKind::Const(const_) => {
            let projection_fun = trait_
                .funs
                .assoc_consts
                .get(&proj_did)
                .expect("Projection did should be in the mapping");
            let projection = projection_fun(&proj_ty_args, &proj_const_args);

            encode_const_check(vcx, deps, const_map, ctx, projection, const_)
        }
    }
}

/// Check whether all generic parameters of the given alias term have alredy been mapped
fn is_alias_ready<'vir>(
    term: &ty::AliasTerm<'vir>,
    ty_map: &FxHashMap<ty::GenericArg<'vir>, vir::ExprTyVal<'vir>>,
    const_map: &FxHashMap<ty::GenericArg<'vir>, vir::ExprSnap<'vir>>,
) -> bool {
    for arg in term.args {
        for arg in arg.walk() {
            match arg.kind() {
                ty::GenericArgKind::Type(ty) => {
                    if let ty::TyKind::Param(_) = ty.kind() {
                        if !ty_map.contains_key(&arg) {
                            return false;
                        }
                    }
                }
                ty::GenericArgKind::Const(_) => {
                    if !const_map.contains_key(&arg) {
                        return false;
                    }
                }
                _ => {}
            }
        }
    }
    true
}

fn process_trait_predicates<'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, TraitImplEnc>,
    ty_map: &FxHashMap<ty::GenericArg<'vir>, vir::ExprTyVal<'vir>>,
    const_map: &FxHashMap<ty::GenericArg<'vir>, vir::ExprSnap<'vir>>,
    ctx: GParams<'vir>,
    trait_preds: impl Iterator<Item = ty::TraitPredicate<'vir>>,
) -> vir::ExprBool<'vir> {
    let tcx = vcx.tcx();
    let mut conjuncts = Vec::new();
    for trait_pred in trait_preds {
        let required_trait_impl_fun = deps
            .require_ref::<TraitEnc>(trait_pred.def_id())
            .unwrap()
            .impl_fun;

        let trait_args = trait_pred.trait_ref.args;
        let ty_args: Vec<_> = trait_args
            .iter()
            .filter_map(|arg| arg.as_type())
            .map(|arg| assemble_type(tcx, deps, &ty_map, &const_map, ctx, arg))
            .collect();

        let const_args: Vec<_> = trait_args
            .iter()
            .filter_map(|arg| arg.as_const())
            .map(|const_| assemble_const(deps, ctx, &const_map, const_).downcast_ty())
            .collect();

        conjuncts.push(required_trait_impl_fun(&ty_args, &const_args));
    }
    vcx.mk_conj(&conjuncts)
}
