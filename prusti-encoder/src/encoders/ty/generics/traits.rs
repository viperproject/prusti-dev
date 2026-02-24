use prusti_rustc_interface::{middle::ty, span::def_id::DefId};
use rustc_hash::FxHashMap;
use std::collections::VecDeque;
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
type AssocTypeFun<'vir> = FunctionIdn<'vir, TraitArgs, vir::TyVal>;
type AssocConstFun<'vir> = FunctionIdn<'vir, TraitArgs, vir::Snap>;
type ImplFun<'vir> = FunctionIdn<'vir, TraitArgs, vir::Bool>;
type ImplUnknownFun<'vir> =
    FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap, vir::Int), vir::Bool>;

#[derive(Debug, Clone)]
pub struct TraitEncOutputRef<'vir> {
    pub trait_name: &'vir str,
    pub funs: TraitFuns<'vir>,
    pub impl_fun: ImplFun<'vir>,
}
impl OutputRefAny for TraitEncOutputRef<'_> {}

#[derive(Debug, Clone)]
pub struct TraitEncOutput<'vir> {
    trait_domain: vir::Domain<'vir>,
    impl_fun: vir::Function<'vir>,
    impl_unknown_fun: vir::Function<'vir>,
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
            program.add_function(trait_enc.impl_unknown_fun);
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

            let trait_items = tcx.associated_items(task_key).in_definition_order();
            let assoc_funs = associated_items_funs(vcx, deps, trait_name, trait_items);

            let vpr_funs = assoc_funs.mk_domain_functions(vcx);

            let impl_fun_idn = FunctionIdn::new(
                vir_format_identifier!(vcx, "{trait_name}_impl"),
                (params.ty_args(), params.const_args()),
                vir::TYPE_BOOL,
            );

            let impl_unknown_fun_idn: ImplUnknownFun = {
                // Omit the `Self` type as it is known to be the "Unknown_type"
                let unknown_args = &params.ty_args()[1..];
                FunctionIdn::new(
                    vir_format_identifier!(vcx, "{trait_name}_unknown_impl"),
                    (unknown_args, params.const_args(), vir::TYPE_INT),
                    vir::TYPE_BOOL,
                )
            };

            // Emit the impl function reference early, so that it can be used to encode caller
            // bounds without causing dependency cycles.
            deps.emit_output_ref(
                *task_key,
                TraitEncOutputRef {
                    trait_name,
                    funs: assoc_funs,
                    impl_fun: impl_fun_idn,
                },
            )?;

            let impl_fun_body = {
                let mut trait_impl_checks = Vec::new();

                for impl_did in tcx.all_impls(*task_key) {
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

                    for (&ty_expr, rust_ty) in std::iter::zip(params.ty_exprs(), trait_rust_tys) {
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

                    if !checks.is_empty() {
                        trait_impl_checks.push(vcx.mk_conj(&checks));
                    }
                }

                {
                    // Case for unknown types
                    let self_expr = params.ty_exprs()[0];

                    let is_unknown_type = vcx.mk_adt_discriminator_expr(self_expr, "Unknown_type");

                    let unknown_id_destructor =
                        vcx.mk_adt_destructor("non_unit", vir::TYPE_TYVAL, vir::TYPE_INT);
                    let extracted_id = unknown_id_destructor.call()(self_expr);

                    let unknown_impls = impl_unknown_fun_idn(
                        &params.ty_exprs()[1..],
                        params.const_exprs(),
                        extracted_id,
                    );

                    let unknown_check = vcx.mk_conj(&[is_unknown_type, unknown_impls]);

                    trait_impl_checks.push(unknown_check);
                }

                vcx.mk_disj(&trait_impl_checks)
            };

            let impl_unknown_fun = vcx.mk_function(
                impl_unknown_fun_idn,
                (
                    &params.ty_decls()[1..],
                    params.const_decls(),
                    vcx.mk_local_decl("non_unit", vir::TYPE_INT),
                ),
                &[],
                &[],
                None,
                None,
            );

            let impl_fun = vcx.mk_function(
                impl_fun_idn,
                (params.ty_decls(), params.const_decls()),
                &[],
                &[],
                None,
                Some(impl_fun_body),
            );

            let trait_domain = vcx.mk_domain(
                vir_format_identifier!(vcx, "t_{trait_name}"),
                &[],
                &[],
                vcx.alloc_slice(vpr_funs.as_slice()),
                None,
            );
            Ok((
                TraitEncOutput {
                    trait_domain,
                    impl_fun,
                    impl_unknown_fun,
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
    ty_map: &mut FxHashMap<ty::GenericArg<'vir>, vir::ExprTyVal<'vir>>,
    const_map: &mut FxHashMap<ty::GenericArg<'vir>, vir::ExprSnap<'vir>>,
    ctx: GParams<'vir>,
    expr: vir::ExprTyVal<'vir>,
    ty: ty::Ty<'vir>,
) -> Option<vir::ExprGenBool<'vir, (), !>> {
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
fn encode_const_check<'a>(
    vcx: &'a vir::VirCtxt<'a>,
    deps: &mut TaskEncoderDependencies<'a, TraitEnc>,
    const_map: &mut HashMap<ty::GenericArg<'a>, vir::ExprSnap<'a>>,
    ctx: GParams<'a>,
    expr: vir::ExprSnap<'a>,
    const_: ty::Const<'a>,
) -> Option<vir::ExprGenBool<'a, (), !>> {
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
    deps: &mut TaskEncoderDependencies<'vir, TraitEnc>,
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
    deps: &mut TaskEncoderDependencies<'vir, TraitEnc>,
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
fn process_projection_predicates<'a>(
    vcx: &'a vir::VirCtxt<'a>,
    deps: &mut TaskEncoderDependencies<'a, TraitEnc>,
    ty_map: &mut FxHashMap<ty::GenericArg<'a>, vir::ExprTyVal<'a>>,
    const_map: &mut FxHashMap<ty::GenericArg<'a>, vir::ExprSnap<'a>>,
    ctx: GParams<'a>,
    projections: impl Iterator<Item = ty::ProjectionPredicate<'a>>,
) -> Option<vir::ExprGenBool<'a, (), !>> {
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

fn process_projection<'a>(
    vcx: &'a vir::VirCtxt<'a>,
    deps: &mut TaskEncoderDependencies<'a, TraitEnc>,
    ty_map: &mut FxHashMap<ty::GenericArg<'a>, vir::ExprTyVal<'a>>,
    const_map: &mut FxHashMap<ty::GenericArg<'a>, vir::ExprSnap<'a>>,
    ctx: GParams<'a>,
    projection: ty::ProjectionPredicate<'a>,
) -> Option<vir::ExprGenBool<'a, (), !>> {
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

fn process_trait_predicates<'a>(
    vcx: &'a vir::VirCtxt<'a>,
    deps: &mut TaskEncoderDependencies<'a, TraitEnc>,
    ty_map: &FxHashMap<ty::GenericArg<'a>, vir::ExprTyVal<'a>>,
    const_map: &FxHashMap<ty::GenericArg<'a>, vir::ExprSnap<'a>>,
    ctx: GParams<'a>,
    trait_preds: impl Iterator<Item = ty::TraitPredicate<'a>>,
) -> vir::ExprGenBool<'a, (), !> {
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

#[derive(Debug, Clone)]
pub struct TraitFuns<'a> {
    pub assoc_types: FxHashMap<DefId, AssocTypeFun<'a>>,
    pub assoc_consts: FxHashMap<DefId, AssocConstFun<'a>>,
}

impl<'a> TraitFuns<'a> {
    fn mk_domain_functions(&self, vcx: &'a vir::VirCtxt<'a>) -> Vec<vir::DomainFunction<'a>> {
        self.assoc_types
            .values()
            .map(|fun| vcx.mk_domain_function(*fun, false, None))
            .chain(
                self.assoc_consts
                    .values()
                    .map(|fun| vcx.mk_domain_function(*fun, false, None)),
            )
            .collect()
    }
}

/// Collect mappings for associated items of a trait to their corresponding VIR functions.
fn associated_items_funs<'a>(
    vcx: &'a vir::VirCtxt<'a>,
    deps: &mut TaskEncoderDependencies<'a, TraitEnc>,
    trait_name: &str,
    assoc_items: impl Iterator<Item = &'a ty::AssocItem>,
) -> TraitFuns<'a> {
    let tcx = vcx.tcx();

    let mut assoc_types = FxHashMap::default();
    let mut assoc_consts = FxHashMap::default();

    let mk_identifier = |item_name, item_type| {
        vir_format_identifier!(vcx, "{trait_name}_assoc_{item_type}_{item_name}")
    };

    for item in assoc_items {
        let assoc_did = item.def_id;
        let name = item.name();
        let params = deps
            .require_dep::<GenericParamsEnc>(GParams::from(assoc_did))
            .unwrap();
        let args = (params.ty_args(), params.const_args());

        match item.kind {
            ty::AssocKind::Type { .. } => {
                let fun = FunctionIdn::new(mk_identifier(name, "type"), args, vir::TYPE_TYVAL);
                assoc_types.insert(assoc_did, fun);
            }
            ty::AssocKind::Const { .. } => {
                let rust_ty = tcx.type_of(assoc_did).skip_binder();
                let decomp = RustTyDecomposition::from_ty(rust_ty, assoc_did);
                let ret_ty = (deps.require_ref::<TyPureEnc>(decomp.ty).unwrap().domain)();

                let fun = FunctionIdn::new(mk_identifier(name, "const"), args, ret_ty);
                assoc_consts.insert(assoc_did, fun);
            }
            ty::AssocKind::Fn { .. } => {
                // unimplemented
            }
        }
    }
    TraitFuns {
        assoc_types,
        assoc_consts,
    }
}
