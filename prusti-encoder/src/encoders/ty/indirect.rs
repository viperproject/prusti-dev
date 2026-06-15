use itertools::Itertools;
use pcg::borrow_pcg::region_projection::{
    ExtractRegionsCtxt, LifetimeProjection, LifetimeProjectionIdx, PcgRegion, Region,
};
use prusti_rustc_interface::{
    index::IndexVec,
    middle::ty::{self, TyCtxt},
};
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, Reify};

use crate::encoders::{TyUseImpureEnc, custom::PairUseEnc, ty::RustTyDecomposition};

use super::{
    data::{StructData, TySpecifics},
    generics::GParams,
    impure::TyImpureEnc,
    interior_mut::TyInteriorMutUseEnc,
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
type SetOutput<'vir> = vir::ExprGenSet<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>;

#[derive(Clone)]
pub struct IndirectPredicatesEncOutputRef<'vir> {
    pub predicate_applications: Vec<ExprOutput<'vir>>,
    /// Sets of `(address, type)` pairs of all interior-mutable objects
    /// reachable through references with the projection's region (collected
    /// by the `_IM` functions of the types behind those references).
    pub interior_mut_sets: Vec<SetOutput<'vir>>,
}

impl<'vir> IndirectPredicatesEncOutputRef<'vir> {
    pub fn new(
        predicate_applications: Vec<ExprOutput<'vir>>,
        interior_mut_sets: Vec<SetOutput<'vir>>,
    ) -> Self {
        Self {
            predicate_applications,
            interior_mut_sets,
        }
    }
}

/// Constructs a quantified permission granting write access to all
/// interior-mutable objects in the union of the given `_IM` sets. A single
/// quantified permission over the union (rather than one per set) ensures
/// that aliased objects, which appear in multiple sets, are counted only once.
pub fn interior_mut_quant_perm<'vir, E: TaskEncoder>(
    vcx: &'vir vir::VirCtxt<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, E>,
    sets: Vec<vir::ExprSet<'vir>>,
) -> Result<vir::ExprBool<'vir>, EncodeFullError<'vir, E>> {
    let pair = deps
        .require_dep::<PairUseEnc>(vec![vir::TYPE_REF.as_dyn(), vir::TYPE_TYVAL.as_dyn()])
        .unwrap();
    // The elements of the `_IM` sets are `(address, type)` pairs of unknown
    // (dynamic) type, so the permission for each element is to the generic
    // (`Param`) predicate at that address.
    let param = RustTyDecomposition::from_ty(vcx.tcx().types.self_param, GParams::empty()).ty;
    let generic_pred = deps.require_dep::<TyImpureEnc>(param)?.data.ref_to_pred;
    let set = sets
        .into_iter()
        .reduce(|acc, e| {
            vcx.mk_anyset_op_expr(vir::CollectionBinOpKind::Union, acc, e)
                .downcast_ty()
        })
        .unwrap_or_else(|| vcx.mk_set_literal_expr(&[], pair.ty));
    let im_decl = vcx.mk_local_decl("im", pair.ty);
    let im = vcx.mk_local_ex(im_decl);
    let in_set = vcx.mk_set_in_expr(im, set);
    let perm = vcx.mk_predicate_app_expr(generic_pred(
        pair.destructors[0].call()(im).downcast_ty::<vir::Ref>(),
        &[pair.destructors[1].call()(im).downcast_ty::<vir::TyVal>()],
        &[],
    )(None));
    let body = vcx
        .mk_bin_op_expr(vir::BinOpKind::Implies, in_set, perm)
        .downcast_ty();
    Ok(vcx.mk_forall_expr(
        vcx.alloc_slice(&[im_decl]),
        vcx.alloc_slice(&[vcx.mk_trigger(&[in_set])]),
        body,
    ))
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
            let mut interior_mut_sets = vec![];
            // The `_IM` sets contain `(address, type)` pairs.
            let pair = deps
                .require_dep::<PairUseEnc>(vec![vir::TYPE_REF.as_dyn(), vir::TYPE_TYVAL.as_dyn()])
                .unwrap();
            let set_ty = vcx.mk_ty_set(pair.ty);
            // Collects (accessor, indirect_predicate) and (accessor,
            // interior_mut_set) pairs for the fields of a struct-like (used
            // for structs and enum variants).
            let collect_field_data =
                |struct_data: StructData<'vir, (RustTyDatas, UsePureTyDatas)>,
                 deps: &mut TaskEncoderDependencies<'vir, IndirectPredicatesEnc>| {
                    let mut preds = vec![];
                    let mut sets = vec![];
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
                            for inner_set in field_indirect.interior_mut_sets {
                                sets.push((accessor, inner_set));
                            }
                        }
                    }
                    Ok((preds, sets))
                };
            match combined.specifics {
                // Optimisation: if there are no type arguments, there cannot be
                // anything behind a ref inside (except for 'static, which we
                // ignore for now). Plus it skips unsupported types if they
                // don't have lifetimes.
                _ if ty.args.args().is_empty() => (),
                TySpecifics::Primitive(_) | TySpecifics::Raw(_) | TySpecifics::Builtin(_) => (),
                // A shared reference gives no direct (write) permission to the
                // place behind it, but it does provide write permission to all
                // interior-mutable objects reachable through it. These are
                // collected by the `_IM` function of the inner type, which
                // itself recurses through everything reachable from the inner
                // type (including nested shared references), so no further
                // recursion is needed here.
                TySpecifics::ImmRef((data, ref_domain)) => {
                    assert_eq!(ty.args.args().len(), 2);
                    let ref_region = PcgRegion::from(ty.args.args()[0].expect_region());
                    if ref_region == task_region {
                        // Normalize the inner type since `value_access` below
                        // returns a snapshot casted to the caller context.
                        let inner_ty = data.referent.decompose_normalize(ty.args);
                        let inner_im = deps.require_dep::<TyInteriorMutUseEnc>(inner_ty)?;
                        let ref_domain = *ref_domain;
                        interior_mut_sets.push(vcx.mk_lazy_expr(
                            "immref_interior_mut",
                            set_ty,
                            Box::new(move |_vcx, self_expr: vir::ExprSnap<'vir>| {
                                let snap = self_expr.downcast_ty();
                                inner_im
                                    .get_all(
                                        ref_domain.deref_access(snap),
                                        ref_domain.value_access(snap),
                                    )
                                    .kind
                            }),
                        ));
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
                        // also provides write permission to all
                        // interior-mutable objects reachable from it. Note
                        // that the inner snapshot is read in the heap state
                        // where this expression ends up (not the state of the
                        // snapshot used for reification).
                        let inner_im = deps.require_dep::<TyInteriorMutUseEnc>(inner_ty)?;
                        interior_mut_sets.push(vcx.mk_lazy_expr(
                            "mutref_interior_mut",
                            set_ty,
                            Box::new(move |_vcx, self_expr: vir::ExprSnap<'vir>| {
                                let addr = ref_domain.deref_access(self_expr.downcast_ty());
                                inner_im.get_all(addr, inner_impure.ref_to_snap(addr)).kind
                            }),
                        ));
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
                        interior_mut_sets.extend(inner_indirect.interior_mut_sets.into_iter().map(
                            |inner_set| {
                                vcx.mk_lazy_expr(
                                    "ref_inner_interior_mut",
                                    set_ty,
                                    Box::new(move |vcx, self_expr: vir::ExprGenSnap<_, _>| {
                                        inner_set
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
                            },
                        ));
                    }
                }
                TySpecifics::StructLike(data) => {
                    // TODO: invalid recursion here if the defined struct is
                    // recursive!
                    let (preds, sets) = collect_field_data(data, deps)?;
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
                    for (accessor, inner_set) in sets {
                        interior_mut_sets.push(vcx.mk_lazy_expr(
                            "struct_field_interior_mut",
                            set_ty,
                            Box::new(move |vcx, self_expr: vir::ExprGenSnap<_, _>| {
                                inner_set
                                    .reify(vcx, accessor.read(self_expr.downcast_ty()))
                                    .kind
                            }),
                        ));
                    }
                }
                TySpecifics::EnumLike(data) => {
                    let snap_to_discr_snap = data.data.1.snap_to_discr_snap;

                    let mut variant_preds = Vec::new();
                    let mut variant_sets = Vec::new();
                    for variant in data.variants {
                        let (preds, sets) = collect_field_data(variant.inner, deps)?;
                        variant_preds.push((variant.data.1.discr, preds));
                        variant_sets.push((variant.data.1.discr, sets));
                    }

                    if variant_preds.is_empty() {
                        return Ok(((), IndirectPredicatesEncOutputRef::new(vec![], vec![])));
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
                    let pair_ty = pair.ty;
                    interior_mut_sets.push(vcx.mk_lazy_expr(
                        "enum_variant_interior_mut",
                        set_ty,
                        Box::new(move |vcx, self_expr: vir::ExprGenSnap<_, _>| {
                            let self_csnap = self_expr.downcast_ty();
                            let self_discr = snap_to_discr_snap.call()(self_csnap);
                            let variant_unions: Vec<_> = variant_sets
                                .iter()
                                .map(|(discr, fields)| {
                                    let union = fields
                                        .iter()
                                        .map(|(acc, set)| set.reify(vcx, acc.read(self_csnap)))
                                        .reduce(|acc, e| {
                                            vcx.mk_anyset_op_expr(
                                                vir::CollectionBinOpKind::Union,
                                                acc,
                                                e,
                                            )
                                            .downcast_ty()
                                        })
                                        .unwrap_or_else(|| vcx.mk_set_literal_expr(&[], pair_ty));
                                    (discr, union)
                                })
                                .collect();
                            let (first, rest) = variant_unions.split_first().unwrap();
                            rest.iter()
                                .fold(first.1, |else_, (discr, set)| {
                                    vcx.mk_ternary_expr(
                                        vir::expr! { ([self_discr]) == ([*discr]) },
                                        *set,
                                        else_,
                                    )
                                })
                                .kind
                        }),
                    ));
                }
            };
            Ok((
                (),
                IndirectPredicatesEncOutputRef::new(predicate_applications, interior_mut_sets),
            ))
        })
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
