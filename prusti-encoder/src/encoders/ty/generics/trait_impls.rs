use std::{collections::VecDeque, iter};

use prusti_rustc_interface::{index::bit_set::DenseBitSet, middle::ty, span::def_id::DefId};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, Domain, vir_format_identifier};

use crate::encoders::{
    ConstEnc,
    r#const::ConstEncTask,
    ty::{
        RustTyDecomposition,
        generics::{GArgs, GArgsTyEnc, GParams, GenericParams, GenericParamsEnc, traits::TraitEnc},
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

            let all_impls = tcx.trait_impls_in_crate(task_key.krate);
            let idx = all_impls.iter().position(|did| did == task_key).unwrap();

            let ctx = GParams::from(*task_key);
            let params = deps.require_dep::<GenericParamsEnc>(ctx)?;

            let trait_ref = tcx.impl_trait_ref(task_key).unwrap().instantiate_identity();
            let trait_did = trait_ref.def_id;
            let trait_data = deps.require_ref::<TraitEnc>(trait_did)?;
            let trait_name = trait_data.trait_name;

            let args = deps.require_dep::<GArgsTyEnc>(GArgs::new(ctx, trait_ref.args))?;
            let mut axioms = Vec::new();

            let implementing_ty = tcx.type_of(task_key).instantiate_identity();
            let implementing_ty = RustTyDecomposition::from_ty(implementing_ty, *task_key);
            let implementing_ty = implementing_ty.ty.name();

            let trait_ty_decls = params.ty_decls().to_vec();
            let trait_const_decls = params.const_decls().to_vec();

            for impl_item in tcx.associated_items(task_key).in_definition_order() {
                let trait_item_def_id = impl_item.trait_item_def_id.unwrap();
                let impl_item_def_id = impl_item.def_id;
                let item_name = tcx.item_name(impl_item_def_id);

                // construct arguments for assoc_item function
                // parameters of the trait are substituted
                // by the arguments used in the impl
                // parameters of the associated type are kept

                // parameters of assoc item include already substituted arguments
                let impl_item_params = GParams::from(impl_item_def_id);
                let assoc_params = deps
                    .require_dep::<GenericParamsEnc>(impl_item_params)
                    .unwrap();

                let assoc_ty_decls = assoc_params.ty_decls();
                let assoc_const_decls = assoc_params.const_decls();

                // Combine substituted trait ty decls with the decls of the associated type
                let mut trait_ty_decls = trait_ty_decls.clone();
                trait_ty_decls.extend_from_slice(&assoc_ty_decls[params.ty_exprs().len()..]);
                let mut trait_const_decls = trait_const_decls.clone();
                trait_const_decls
                    .extend_from_slice(&assoc_const_decls[params.const_exprs().len()..]);

                // Combine substituted trait params with the params of the associated type
                let trait_tys = vcx.alloc_slice(
                    &iter::empty()
                        .chain(args.get_ty().to_owned())
                        .chain(assoc_params.ty_exprs()[params.ty_exprs().len()..].to_owned())
                        .collect::<Vec<_>>(),
                );
                let trait_consts = vcx.alloc_slice(
                    &iter::empty()
                        .chain(args.get_const().to_owned())
                        .chain(assoc_params.const_exprs()[params.const_exprs().len()..].to_owned())
                        .collect::<Vec<_>>(),
                );

                match impl_item.kind {
                    ty::AssocKind::Type { .. } => {
                        let assoc_type =
                            trait_data.fns.assoc_types.get(&trait_item_def_id).unwrap();

                        // the type we want to resolve the type alias to
                        let assoc_type_expr = assoc_params.ty_expr(
                            deps,
                            RustTyDecomposition::from_ty(
                                tcx.type_of(impl_item_def_id).instantiate_identity(),
                                impl_item_params,
                            ),
                        );
                        axioms.push(vcx.mk_domain_axiom(
                            vir_format_identifier!(vcx, "{trait_name}_impl_{implementing_ty}_{idx}_assoc_type_{item_name}"),
                            vir::expr! {forall ..[trait_ty_decls], ..[trait_const_decls] :: {[assoc_type(trait_tys, trait_consts)]} ([assoc_type(trait_tys, trait_consts)]) == (assoc_type_expr)},
                        ));
                    }
                    _ => { /* unimplementd */ }
                }
            }

            let impl_condition = impl_block_condition(vcx, deps, *task_key);

            Ok((
                vcx.mk_domain(
                    vir_format_identifier!(vcx, "trait_{trait_name}_impl_{implementing_ty}_{idx}"),
                    &[],
                    vcx.alloc_slice(&axioms),
                    &[],
                    None,
                ),
                TraitImplEncOutput { impl_condition },
            ))
        })
    }
}

fn bitset_from(iter: impl IntoIterator<Item = u32>, size: usize) -> DenseBitSet<u32> {
    iter.into_iter()
        .fold(DenseBitSet::new_empty(size), |mut acc, idx| {
            acc.insert(idx);
            acc
        })
}
fn projection_deps<'vir>(
    projection: ty::ProjectionPredicate<'vir>,
    generics_count: usize,
) -> (DenseBitSet<u32>, DenseBitSet<u32>) {
    let generic_idx = |arg: ty::GenericArg| match arg.kind() {
        ty::GenericArgKind::Type(ty) if let ty::TyKind::Param(p) = ty.kind() => Some(p.index),
        ty::GenericArgKind::Const(const_) if let ty::ConstKind::Param(p) = const_.kind() => {
            Some(p.index)
        }
        _ => None,
    };

    let required = projection
        .projection_term
        .args
        .iter()
        .flat_map(|arg| arg.walk().filter_map(generic_idx));

    let produced = projection.term.walk().filter_map(generic_idx);

    (
        bitset_from(required, generics_count),
        bitset_from(produced, generics_count),
    )
}

fn order_projections<'vir>(
    known_generics: impl IntoIterator<Item = u32>,
    projections: impl IntoIterator<Item = ty::ProjectionPredicate<'vir>>,
    generics_count: usize,
) -> Vec<ty::ProjectionPredicate<'vir>> {
    let mut known_generics = bitset_from(known_generics, generics_count);

    let mut worklist: VecDeque<_> = projections
        .into_iter()
        .map(|p| (p, projection_deps(p, generics_count)))
        .collect();

    let mut ordered = Vec::new();

    while let Some((proj, (required, produced))) = worklist.pop_front() {
        if known_generics.superset(&required) {
            known_generics.union(&produced);
            ordered.push(proj);
        } else {
            worklist.push_back((proj, (required, produced)));
        }
    }

    ordered
}

fn discover_bind_points<'vir>(
    deps: &mut TaskEncoderDependencies<'vir, TraitImplEnc>,
    generic_map: &mut GenericsMap<'vir>,
    ctx: GParams<'vir>,
    expr: vir::ExprDyn<'vir>,
    ty: ty::Ty<'vir>,
) {
    dbg!(&ty);

    if let ty::TyKind::Param(p) = ty.kind() {
        generic_map.try_insert(p.index, expr);
        return;
    }

    let decomp = RustTyDecomposition::from_ty(ty, ctx);
    let ty_enc = deps.require_ref::<TyConstructorEnc>(decomp.ty).unwrap();

    let args = decomp.args.args();
    let inner_types = args.iter().filter_map(|arg| arg.as_type());
    for (i, inner_ty) in inner_types.enumerate() {
        let accessor = ty_enc.ty_param_accessors[i];
        let inner_expr = accessor.call()(expr.downcast_ty());

        discover_bind_points(deps, generic_map, ctx, inner_expr.upcast_ty(), inner_ty);
    }

    let inner_consts = args.iter().filter_map(|arg| arg.as_const());
    for (i, inner_const) in inner_consts.enumerate() {
        let accessor = ty_enc.const_param_accessors[i];
        let inner_expr = accessor.call()(expr.downcast_ty());

        if let ty::ConstKind::Param(p) = inner_const.kind() {
            generic_map.try_insert(p.index, inner_expr.upcast_ty());
        }
    }
}

fn impl_block_condition<'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, TraitImplEnc>,
    impl_did: DefId,
) -> vir::ExprBool<'vir> {
    let tcx = vcx.tcx();
    let impl_ctx = GParams::from(impl_did).with_suffix("impl");

    let trait_ref = tcx.impl_trait_ref(impl_did).unwrap().instantiate_identity();

    let trait_ctx = GParams::from(trait_ref.def_id).with_suffix("trait");
    let trait_params = deps.require_dep::<GenericParamsEnc>(trait_ctx).unwrap();
    let impl_params = deps.require_dep::<GenericParamsEnc>(impl_ctx).unwrap();

    let impl_args = deps
        .require_dep::<GArgsTyEnc>(GArgs::new(impl_ctx, trait_ref.args))
        .unwrap();
    let impl_ty_args = impl_args.get_ty();
    let trait_ty_params = trait_params.ty_exprs();
    let trait_const_params = trait_params.const_exprs();

    // Collect the bindings for the generics of this impl block
    let mut generics_map = GenericsMap::new(impl_ctx.count());
    collect_bindings(
        deps,
        &mut generics_map,
        trait_ctx,
        &trait_params,
        trait_ref.args,
    );

    let mut checks = Vec::new();
    for (trait_ty_param, impl_ty_arg) in std::iter::zip(trait_ty_params, impl_ty_args) {
        checks.push(vcx.mk_eq_expr(trait_ty_param, impl_ty_arg));
    }

    let caller_bounds = impl_ctx.typing_env().param_env.caller_bounds();

    let trait_preds = caller_bounds
        .iter()
        .filter_map(ty::Clause::as_trait_clause)
        .map(ty::Binder::skip_binder);

    for trait_pred in trait_preds {
        let trait_did = trait_pred.def_id();
        let trait_ = deps.require_ref::<TraitEnc>(trait_did).unwrap();
        let gargs = GArgs::new(impl_ctx, trait_pred.trait_ref.args);
        let gargs = deps.require_dep::<GArgsTyEnc>(gargs).unwrap();

        let impl_check = (trait_.impl_fun)(gargs.get_ty(), gargs.get_const());
        dbg!(&impl_check);
        checks.push(impl_check);
    }

    let proj_preds = caller_bounds
        .iter()
        .filter_map(ty::Clause::as_projection_clause)
        .map(ty::Binder::skip_binder);

    let proj_preds = order_projections(generics_map.keys(), proj_preds, impl_ctx.count());

    for proj_pred in proj_preds {
        let trait_did = proj_pred.trait_def_id(tcx);
        let trait_ = deps.require_ref::<TraitEnc>(trait_did).unwrap();
        let gargs = GArgs::new(impl_ctx, proj_pred.projection_term.args);
        let gargs = deps.require_dep::<GArgsTyEnc>(gargs).unwrap();

        let (projection, expr): (vir::ExprDyn, vir::ExprDyn) = match proj_pred.term.kind() {
            ty::TermKind::Ty(ty) => {
                let projection =
                    trait_.fns.assoc_types[&proj_pred.def_id()](gargs.get_ty(), gargs.get_const());
                let decomp = RustTyDecomposition::from_ty(ty, impl_ctx);
                let ty_expr = impl_params.ty_expr(deps, decomp);
                discover_bind_points(
                    deps,
                    &mut generics_map,
                    impl_ctx,
                    projection.upcast_ty(),
                    ty,
                );
                (projection.upcast_ty(), ty_expr.upcast_ty())
            }
            ty::TermKind::Const(const_) => {
                let projection =
                    trait_.fns.assoc_consts[&proj_pred.def_id()](gargs.get_ty(), gargs.get_const());
                let ty = tcx.type_of(proj_pred.def_id()).instantiate_identity();
                let const_task = ConstEncTask::Ty {
                    const_,
                    ty,
                    context: impl_ctx,
                };
                let const_expr = deps.require_dep::<ConstEnc>(const_task).unwrap();
                if let ty::ConstKind::Param(p) = const_.kind() {
                    generics_map.try_insert(p.index, const_expr.upcast_ty());
                }
                (projection.upcast_ty(), const_expr.upcast_ty())
            }
        };

        let projection_check = vcx.mk_eq_expr(projection, expr);
        dbg!(&projection_check);
        checks.push(projection_check);
    }

    dbg!(&checks);
    dbg!(&generics_map);

    let checks = vcx.mk_conj(&checks);

    dbg!(
        generics_map
            .insertion_ordered()
            .rfold(checks, |acc, (idx, expr)| {
                let idx = impl_params.map_idx(idx);
                let decl = match idx {
                    Result::Ok(idx) => impl_params.ty_decls()[idx].upcast_ty(),
                    Result::Err(idx) => impl_params.const_decls()[idx].upcast_ty(),
                };
                vcx.mk_let_expr(decl, expr, acc)
            })
    )
}

fn collect_bindings<'vir>(
    deps: &mut TaskEncoderDependencies<'vir, TraitImplEnc>,
    generics_map: &mut GenericsMap<'vir>,
    trait_ctx: GParams<'vir>,
    trait_params: &GenericParams<'vir>,
    trait_args: ty::GenericArgsRef<'vir>,
) {
    // Walk the trait type generic arguments
    let impl_rust_tys = trait_args.iter().filter_map(|arg| arg.as_type());
    for (ty_arg, rust_ty) in std::iter::zip(trait_params.ty_exprs(), impl_rust_tys) {
        discover_bind_points(deps, generics_map, trait_ctx, ty_arg.upcast_ty(), rust_ty);
    }

    // Walk the trait const generic arguments
    let impl_rust_consts = trait_args.iter().filter_map(|arg| arg.as_const());
    for (const_arg, rust_const) in std::iter::zip(trait_params.const_exprs(), impl_rust_consts) {
        if let ty::ConstKind::Param(p) = rust_const.kind() {
            generics_map.try_insert(p.index, const_arg.upcast_ty());
        }
    }
}

#[derive(Clone, Debug)]
struct GenericsMap<'vir> {
    present: usize,
    map: Vec<Option<(usize, vir::ExprDyn<'vir>)>>,
}

impl<'vir> GenericsMap<'vir> {
    fn new(size: usize) -> Self {
        GenericsMap {
            present: 0,
            map: vec![None; size],
        }
    }
    fn try_insert(&mut self, idx: u32, expr: vir::ExprDyn<'vir>) -> bool {
        let idx = idx as usize;
        if self.map[idx].is_some() {
            return false;
        }
        self.map[idx] = Some((self.present, expr));
        self.present += 1;
        true
    }

    fn insertion_ordered(
        &self,
    ) -> impl Iterator<Item = (u32, vir::ExprDyn<'vir>)> + DoubleEndedIterator {
        let mut ordered = self
            .map
            .iter()
            .enumerate()
            .filter_map(|(idx, opt)| opt.map(|(order, expr)| (order, (idx as u32, expr))))
            .collect::<Vec<_>>();
        ordered.sort_by_key(|(order, _)| *order);
        ordered.into_iter().map(|(_, (idx, expr))| (idx, expr))
    }

    fn keys(&self) -> impl Iterator<Item = u32> {
        self.map
            .iter()
            .enumerate()
            .filter_map(|(idx, opt)| opt.as_ref().map(|_| idx as u32))
    }
}
