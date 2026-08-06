use itertools::Itertools;
use pcg::borrow_pcg::region_projection::{
    ExtractRegionsCtxt, LifetimeProjection, LifetimeProjectionIdx, PcgRegion, Region,
};
use prusti_rustc_interface::{
    index::IndexVec,
    middle::ty::{self, TyCtxt},
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, Reify};

use crate::encoders::{TyUseImpureEnc, ty::RustTyDecomposition};

use super::{
    data::{StructData, TySpecifics},
    interior_mut::{
        IM_LEVELS, ImTys, MapUnionEnc, MapUnionFns, QpToMapEnc, QpToMapFn, TyInteriorMutUseEnc,
        TyInteriorMutUseExpr, fold_pairs,
    },
    rust_ty::RustTyDatas,
    use_pure::{TyUsePureEnc, UsePureTyDatas},
};

#[derive(Copy, Clone)]
pub struct PrustiPcgCtxt;

impl<'tcx> ExtractRegionsCtxt<'tcx, RustTyDecomposition<'tcx>, PcgRegion<'tcx>> for PrustiPcgCtxt {
    fn extract_regions(
        self,
        data: RustTyDecomposition<'tcx>,
    ) -> IndexVec<LifetimeProjectionIdx<Region>, PcgRegion<'tcx>> {
        data.args
            .args()
            .iter()
            .flat_map(|arg| arg.walk())
            .filter_map(|arg| arg.as_region().map(PcgRegion::from))
            .unique()
            .collect()
    }
}

pub struct IndirectPredicatesEnc;

type ExprInput<'vir> = vir::ExprSnap<'vir>;
type ExprOutput<'vir> = vir::ExprGenBool<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>;
type PairOutput<'vir> = vir::ExprGen<'vir, ExprInput<'vir>, vir::ExprKind<'vir>, vir::Pair>;

#[derive(Clone)]
pub struct IndirectPredicatesEncOutputRef<'vir> {
    pub predicate_applications: Vec<ExprOutput<'vir>>,
    /// Per IM level, the `(owned, shared)` permission-map pairs of the
    /// interior-mutable objects reachable through references with the
    /// projection's region.
    pub interior_mut_pairs: [Vec<PairOutput<'vir>>; IM_LEVELS],
}

impl<'vir> IndirectPredicatesEncOutputRef<'vir> {
    pub fn new(
        predicate_applications: Vec<ExprOutput<'vir>>,
        interior_mut_pairs: [Vec<PairOutput<'vir>>; IM_LEVELS],
    ) -> Self {
        Self {
            predicate_applications,
            interior_mut_pairs,
        }
    }
}

impl<'vir> task_encoder::OutputRefAny for IndirectPredicatesEncOutputRef<'vir> {}

fn projection_region<'tcx>(
    proj: &LifetimeProjection<'tcx, RustTyDecomposition<'tcx>, Region>,
) -> PcgRegion<'tcx> {
    let regions = PrustiPcgCtxt.extract_regions(proj.base());
    regions[proj.region_idx()]
}

impl TaskEncoder for IndirectPredicatesEnc {
    task_encoder::encoder_cache!(IndirectPredicatesEnc);
    const ENCODER_NAME: &'static str = "indirect predicates encoder";

    type TaskDescription<'vir> = LifetimeProjection<'vir, RustTyDecomposition<'vir>, Region>;

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type EncodingError = ();

    type OutputFullDependency<'vir> = IndirectPredicatesEncOutputRef<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        vir::with_vcx(|vcx| {
            let task_region = projection_region(task_key);
            let ty = task_key.base();
            let self_ty_enc = deps.require_dep::<TyUsePureEnc>(ty)?;
            let combined = ty.ty.zip(self_ty_enc);
            let mut predicate_applications = vec![];
            let mut interior_mut_pairs: [Vec<PairOutput<'vir>>; IM_LEVELS] = [vec![], vec![]];
            let tys = ImTys::new(deps);
            let unions = deps.require_dep::<MapUnionEnc>(())?;
            // The `qp_to_map` function, used to materialize the level-0 IM-QP
            // `Map` snapshot passed to level-1 functions.
            let qp_to_map = deps.require_dep::<QpToMapEnc>(())?;
            // Collects (accessor, indirect_predicate) and per-level
            // (accessor, pair) entries for the fields of a struct-like (used
            // for structs and enum variants).
            let collect_field_data =
                |struct_data: StructData<'vir, (RustTyDatas, UsePureTyDatas)>,
                 deps: &mut TaskEncoderDependencies<'vir, IndirectPredicatesEnc>| {
                    let mut preds = vec![];
                    let mut pairs: [Vec<(_, PairOutput<'vir>)>; IM_LEVELS] = [vec![], vec![]];
                    for (field_ty, accessor) in struct_data.fields {
                        let field_ty = field_ty.decompose_context(ty.ty.params, ty.args);
                        if let Some(new_projection) =
                            LifetimeProjection::new(field_ty, task_region, None, PrustiPcgCtxt)
                        {
                            let field_indirect =
                                deps.require_dep::<IndirectPredicatesEnc>(new_projection)?;
                            for inner_expr in field_indirect.predicate_applications {
                                preds.push((accessor, inner_expr));
                            }
                            for (level, ps) in
                                field_indirect.interior_mut_pairs.into_iter().enumerate()
                            {
                                for p in ps {
                                    pairs[level].push((accessor, p));
                                }
                            }
                        }
                    }
                    Ok((preds, pairs))
                };
            match combined.specifics {
                // Optimisation: if there are no type arguments, there cannot be
                // anything behind a ref inside (except for 'static, which we
                // ignore for now). Plus it skips unsupported types if they
                // don't have lifetimes.
                _ if ty.args.args().is_empty() => (),
                TySpecifics::Primitive(_) | TySpecifics::Raw(_) | TySpecifics::Builtin(_) => (),
                // A shared reference gives no direct (write) permission to the
                // place behind it, but it does provide access to all
                // interior-mutable objects reachable through it. These are
                // collected by the `_IM_N` functions of the inner type, which
                // themselves recurse through everything reachable from the
                // inner type (including nested shared references), so no
                // further recursion is needed here.
                TySpecifics::ImmRef((data, ref_domain)) => {
                    assert_eq!(ty.args.args().len(), 2);
                    let ref_region = PcgRegion::from(ty.args.args()[0].expect_region());
                    if ref_region == task_region {
                        // Compute the referent's IM maps generically (as a
                        // `Param`): `decompose_context` keeps the inner type a
                        // `Param` (substituting the concrete type argument), and
                        // `value_access_generic` gives the raw `s_Param` value
                        // behind the reference. This yields `s_Param_IM_N(deref,
                        // param_val, RefCell_type)` rather than
                        // `s_RefCell_IM_N(deref, make_concrete(..), i32)`.
                        let inner_ty = data.referent.decompose_context(ty.ty.params, ty.args);
                        let inner_im = deps.require_dep::<TyInteriorMutUseEnc>(inner_ty)?;
                        let ref_domain = *ref_domain;
                        for (level, pairs) in interior_mut_pairs.iter_mut().enumerate() {
                            let tys_c = tys.clone();
                            pairs.push(vcx.mk_lazy_expr(
                                "immref_interior_mut",
                                tys.result.ty,
                                Box::new(move |_vcx, self_expr: vir::ExprSnap<'vir>| {
                                    let snap = self_expr.downcast_ty();
                                    let addr = ref_domain.deref_access(snap);
                                    let val =
                                        ref_domain.value_access_generic(snap).upcast_ty();
                                    let p = source_pair(
                                        &tys_c, &unions, qp_to_map, inner_im, level, addr, val,
                                    );
                                    // Crossing a `&`: the referent's whole pair
                                    // collapses into the shared side.
                                    let (o, s) = tys_c.split(p);
                                    tys_c
                                        .cons(tys_c.empty_map(), unions.disjoint.call()(o, s))
                                        .kind
                                }),
                            ));
                        }
                    }
                }
                // TODO: it's not valid to have nothing for these. We should fix
                // this by using an opaque predicate to represent potential
                // indirect stuff. For example:
                // fn foo<'a, T: Trait<'a>>(x: T) -> &'a mut i32 { x.get() }
                // Here, `T` could be instantiated as `&'a mut i32` in which
                // case we would want a wand with `i32(result) --* opaque_behind_a(x)`.
                // This is why we should return `opaque_behind_a(x)` here.
                TySpecifics::Param(_) | TySpecifics::Opaque(_) | TySpecifics::ArrayLike(_) => (),
                TySpecifics::MutRef((data, ref_domain)) => {
                    let inner_ty = data.referent.decompose_context(ty.ty.params, ty.args);
                    let inner_impure = deps.require_dep::<TyUseImpureEnc>(inner_ty)?;
                    let ref_region = PcgRegion::from(ty.args.args()[0].expect_region());
                    if ref_region == task_region {
                        predicate_applications.push(vcx.mk_lazy_expr(
                            "ref_indirect",
                            vir::TYPE_BOOL,
                            Box::new(move |vcx, self_expr: vir::ExprSnap<'vir>| {
                                let addr = ref_domain.deref_access(self_expr.downcast_ty());
                                inner_impure.ref_to_pred(vcx, addr, None).kind
                            }),
                        ));
                        // Along with the place behind it, a mutable reference
                        // also provides access to all interior-mutable objects
                        // reachable from it, preserving the owned/shared split.
                        // Note that the inner snapshot is read in the heap state
                        // where this expression ends up (not the state of the
                        // snapshot used for reification).
                        let inner_im = deps.require_dep::<TyInteriorMutUseEnc>(inner_ty)?;
                        for (level, pairs) in interior_mut_pairs.iter_mut().enumerate() {
                            let tys_c = tys.clone();
                            pairs.push(vcx.mk_lazy_expr(
                                "mutref_interior_mut",
                                tys.result.ty,
                                Box::new(move |_vcx, self_expr: vir::ExprSnap<'vir>| {
                                    let addr =
                                        ref_domain.deref_access(self_expr.downcast_ty());
                                    let val = inner_impure.ref_to_snap(addr);
                                    source_pair(
                                        &tys_c, &unions, qp_to_map, inner_im, level, addr, val,
                                    )
                                    .kind
                                }),
                            ));
                        }
                    }
                    if let Some(new_projection) =
                        LifetimeProjection::new(inner_ty, task_region, None, PrustiPcgCtxt)
                    {
                        let inner_indirect =
                            deps.require_dep::<IndirectPredicatesEnc>(new_projection)?;
                        predicate_applications.extend(
                            inner_indirect
                                .predicate_applications
                                .into_iter()
                                .map(|inner_expr| {
                                    vcx.mk_lazy_expr(
                                        "ref_inner_indirect",
                                        vir::TYPE_BOOL,
                                        Box::new(move |vcx, self_expr: vir::ExprGenSnap<_, _>| {
                                            inner_expr
                                                .reify(
                                                    vcx,
                                                    inner_impure.ref_to_snap(
                                                        ref_domain
                                                            .deref_access(self_expr.downcast_ty()),
                                                    ),
                                                )
                                                .kind
                                        }),
                                    )
                                }),
                        );
                        // Nested projections through the `&mut`: crossing a
                        // `&mut` preserves the owned/shared split, so the inner
                        // pairs pass through unchanged (reified with the
                        // referent's snapshot).
                        for (level, ps) in
                            inner_indirect.interior_mut_pairs.into_iter().enumerate()
                        {
                            for inner_pair in ps {
                                interior_mut_pairs[level].push(vcx.mk_lazy_expr(
                                    "ref_inner_interior_mut",
                                    tys.result.ty,
                                    Box::new(move |vcx, self_expr: vir::ExprGenSnap<_, _>| {
                                        inner_pair
                                            .reify(
                                                vcx,
                                                inner_impure.ref_to_snap(
                                                    ref_domain
                                                        .deref_access(self_expr.downcast_ty()),
                                                ),
                                            )
                                            .kind
                                    }),
                                ));
                            }
                        }
                    }
                }
                TySpecifics::StructLike(data) => {
                    // TODO: invalid recursion here if the defined struct is
                    // recursive!
                    let (preds, pairs) = collect_field_data(data, deps)?;
                    for (accessor, inner_expr) in preds {
                        predicate_applications.push(vcx.mk_lazy_expr(
                            "struct_field_indirect",
                            vir::TYPE_BOOL,
                            Box::new(move |vcx, self_expr: vir::ExprGenSnap<_, _>| {
                                inner_expr
                                    .reify(vcx, accessor.read(self_expr.downcast_ty()))
                                    .kind
                            }),
                        ));
                    }
                    for (level, ps) in pairs.into_iter().enumerate() {
                        for (accessor, pair_expr) in ps {
                            interior_mut_pairs[level].push(vcx.mk_lazy_expr(
                                "struct_field_interior_mut",
                                tys.result.ty,
                                Box::new(move |vcx, self_expr: vir::ExprGenSnap<_, _>| {
                                    pair_expr
                                        .reify(vcx, accessor.read(self_expr.downcast_ty()))
                                        .kind
                                }),
                            ));
                        }
                    }
                }
                TySpecifics::EnumLike(data) => {
                    let snap_to_discr_snap = data.data.1.snap_to_discr_snap;

                    let mut variant_preds = Vec::new();
                    let mut variant_pairs: [Vec<(_, Vec<(_, PairOutput<'vir>)>)>; IM_LEVELS] =
                        [vec![], vec![]];
                    for variant in data.variants {
                        let (preds, pairs) = collect_field_data(variant.inner, deps)?;
                        variant_preds.push((variant.data.1.discr, preds));
                        for (level, ps) in pairs.into_iter().enumerate() {
                            variant_pairs[level].push((variant.data.1.discr, ps));
                        }
                    }

                    if variant_preds.is_empty() {
                        return Ok((
                            (),
                            IndirectPredicatesEncOutputRef::new(vec![], [vec![], vec![]]),
                        ));
                    }

                    predicate_applications.push(vcx.mk_lazy_expr(
                        "enum_variant_indirect",
                        vir::TYPE_BOOL,
                        Box::new(move |vcx, self_expr: vir::ExprGenSnap<_, _>| {
                            let self_csnap = self_expr.downcast_ty();
                            let self_discr = snap_to_discr_snap.call()(self_csnap);
                            let variant_conjs: Vec<_> = variant_preds
                                .iter()
                                .map(|(discr, fields)| {
                                    let preds: Vec<_> = fields
                                        .iter()
                                        .map(|(acc, expr)| expr.reify(vcx, acc.read(self_csnap)))
                                        .collect();
                                    (discr, vcx.mk_conj(&preds))
                                })
                                .collect();
                            let (first, rest) = variant_conjs.split_first().unwrap();
                            rest.iter()
                                .fold(first.1, |else_, (discr, conj)| {
                                    vcx.mk_ternary_expr(
                                        vir::expr! { ([self_discr]) == ([*discr]) },
                                        *conj,
                                        else_,
                                    )
                                })
                                .kind
                        }),
                    ));
                    // Per level: a ternary over the variants, each variant's
                    // field pairs merged component-wise.
                    for (level, variants) in variant_pairs.into_iter().enumerate() {
                        let tys_c = tys.clone();
                        interior_mut_pairs[level].push(vcx.mk_lazy_expr(
                            "enum_variant_interior_mut",
                            tys.result.ty,
                            Box::new(move |vcx, self_expr: vir::ExprGenSnap<_, _>| {
                                let self_csnap = self_expr.downcast_ty();
                                let self_discr = snap_to_discr_snap.call()(self_csnap);
                                let variant_merges: Vec<_> = variants
                                    .iter()
                                    .map(|(discr, fields)| {
                                        let ps = fields.iter().map(|(acc, pair_expr)| {
                                            pair_expr.reify(vcx, acc.read(self_csnap))
                                        });
                                        (discr, fold_pairs(&tys_c, &unions, ps))
                                    })
                                    .collect();
                                let (first, rest) = variant_merges.split_first().unwrap();
                                rest.iter()
                                    .fold(first.1, |else_, (discr, pair)| {
                                        vcx.mk_ternary_expr(
                                            vir::expr! { ([self_discr]) == ([*discr]) },
                                            *pair,
                                            else_,
                                        )
                                    })
                                    .kind
                            }),
                        ));
                    }
                }
            };
            Ok((
                (),
                IndirectPredicatesEncOutputRef::new(predicate_applications, interior_mut_pairs),
            ))
        })
    }
}

/// The `(owned, shared)` pair of a referent reachable through a reference, per
/// level: the level-1 call gets its `im_0_map` argument materialized from the
/// referent's own level-0 maps.
fn source_pair<'vir, Curr: 'vir, Next: 'vir>(
    tys: &ImTys<'vir>,
    unions: &MapUnionFns<'vir>,
    qp_to_map: QpToMapFn<'vir>,
    im: TyInteriorMutUseExpr<'vir>,
    level: usize,
    addr: vir::ExprGenRef<'vir, Curr, Next>,
    val: vir::ExprGenSnap<'vir, Curr, Next>,
) -> vir::ExprGen<'vir, Curr, Next, vir::Pair> {
    match level {
        0 => im.get_0(addr, val),
        1 => {
            let (o, s) = tys.split(im.get_0(addr, val));
            let m0 = unions.disjoint.call()(o, s);
            im.get_1(addr, val, qp_to_map.call()(m0))
        }
        _ => unreachable!(),
    }
}

pub fn projection_for_generalized_idx<'tcx>(
    ty: ty::Ty<'tcx>,
    idx: LifetimeProjectionIdx<pcg::borrow_pcg::region_projection::Generalized>,
    decomp: RustTyDecomposition<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<LifetimeProjection<'tcx, RustTyDecomposition<'tcx>, Region>> {
    use pcg::borrow_pcg::GeneralizedLifetime;
    let lifetimes: IndexVec<_, GeneralizedLifetime<'tcx>> = tcx.extract_regions(ty);
    let region = match lifetimes.get(idx)? {
        GeneralizedLifetime::Region(r) => *r,
        GeneralizedLifetime::RegionsIn(_) => return None,
    };
    LifetimeProjection::new(decomp, region, None, PrustiPcgCtxt)
}
