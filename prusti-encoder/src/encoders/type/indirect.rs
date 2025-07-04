use prusti_rustc_interface::middle::ty::{self};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, Reify};

use super::{rust_ty_predicates::RustTyPredicatesEnc, rust_ty_snapshots::RustTySnapshotsEnc};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IndirectKey {
    Early(ty::EarlyParamRegion),
    Late(ty::BoundRegionKind),
    Var(ty::RegionVid),
    Param(ty::ParamTy),
}

impl IndirectKey {
    pub fn from_generic_arg(ga: ty::GenericArg) -> Option<Self> {
        match ga.unpack() {
            ty::GenericArgKind::Lifetime(region) => Self::from_region(region),
            ty::GenericArgKind::Type(ty) => match *ty.kind() {
                ty::TyKind::Param(p) => Some(IndirectKey::Param(p)),
                _ => None,
            },
            ty::GenericArgKind::Const(_) => None,
        }
    }

    pub fn from_region(region: ty::Region) -> Option<Self> {
        use ty::RegionKind;
        match region.kind() {
            RegionKind::ReEarlyParam(e) => Some(IndirectKey::Early(e)),
            RegionKind::ReBound(_, g) => Some(IndirectKey::Late(g.kind)),
            RegionKind::ReVar(r) => Some(IndirectKey::Var(r)),
            RegionKind::RePlaceholder(..)
            | RegionKind::ReError(..)
            | RegionKind::ReErased
            | RegionKind::ReLateParam(..) => unreachable!("{region:?}"),
            RegionKind::ReStatic => None,
        }
    }
}

pub struct IndirectPredicatesEnc;

type ExprInput<'vir> = vir::ExprSnap<'vir>;
type ExprOutput<'vir> = vir::ExprGenBool<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>;

#[derive(Clone)]
pub struct IndirectPredicatesEncOutputRef<'vir> {
    pub covariant: Vec<ExprOutput<'vir>>,
    pub contravariant: Vec<ExprOutput<'vir>>,
}

impl<'vir> task_encoder::OutputRefAny for IndirectPredicatesEncOutputRef<'vir> {}

impl TaskEncoder for IndirectPredicatesEnc {
    task_encoder::encoder_cache!(IndirectPredicatesEnc);

    type TaskDescription<'vir> = (ty::Ty<'vir>, IndirectKey);

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type EncodingError = ();

    type OutputRef<'vir> = IndirectPredicatesEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let (ty, proj_region) = task_key;
            let self_ty_enc = deps.require_local::<RustTySnapshotsEnc>(*ty)?;
            let mut covariant = Vec::<ExprOutput<'vir>>::new();
            let mut contravariant = Vec::<ExprOutput<'vir>>::new();
            match ty.kind() {
                ty::TyKind::Ref(ref_region, inner_ty, ty::Mutability::Mut) => {
                    let ref_domain = self_ty_enc.generic_snapshot.specifics.expect_mutref();
                    if IndirectKey::from_region(*ref_region)
                        .is_some_and(|indirect| &indirect == proj_region)
                    {
                        let inner_ty_enc = deps.require_ref::<RustTyPredicatesEnc>(*inner_ty)?;
                        covariant.push(vcx.mk_lazy_expr(
                            "ref_indirect",
                            vir::TYPE_BOOL,
                            Box::new(move |vcx, self_expr| {
                                inner_ty_enc
                                    .ref_to_pred(
                                        vcx,
                                        (ref_domain.deref_access)(self_expr.downcast_ty()),
                                        None,
                                    )
                                    .kind
                            }),
                        ));
                    }
                    // TODO: is this correct??? do we always project into the inner type, regardless of region?
                    let inner_indirect =
                        deps.require_ref::<IndirectPredicatesEnc>((*inner_ty, *proj_region))?;
                    let inner = inner_indirect
                        .covariant
                        .into_iter()
                        .chain(inner_indirect.contravariant)
                        .map(|inner_expr| {
                            vcx.mk_lazy_expr(
                                "ref_inner_indirect",
                                vir::TYPE_BOOL,
                                Box::new(move |vcx, self_expr: vir::ExprGenSnap<_, _>| {
                                    inner_expr
                                        .reify(
                                            vcx,
                                            (ref_domain.value_access)(self_expr.downcast_ty())
                                                .upcast_ty(),
                                        )
                                        .kind
                                }),
                            )
                        })
                        .collect::<Vec<_>>();
                    covariant.extend(inner.clone());
                    contravariant.extend(inner);
                }
                ty::TyKind::Tuple(params) => {
                    let field_accessors = self_ty_enc
                        .generic_snapshot
                        .specifics
                        .expect_structlike()
                        .field_access;
                    for (field_ty, accessor) in params.into_iter().zip(field_accessors) {
                        let project = |inner_expr: ExprOutput<'vir>| {
                            vcx.mk_lazy_expr(
                                "ref_inner_indirect",
                                vir::TYPE_BOOL,
                                Box::new(move |vcx, self_expr: vir::ExprGenSnap<_, _>| {
                                    inner_expr
                                        .reify(vcx, (accessor.read)(self_expr.downcast_ty()))
                                        .kind
                                }),
                            )
                        };

                        // TODO: tuple generics need to be passed to field accessors
                        // TODO: tuple fields need to be (snapshot) cast
                        let field_indirect =
                            deps.require_ref::<IndirectPredicatesEnc>((field_ty, *proj_region))?;
                        covariant.extend(field_indirect.covariant.into_iter().map(project));
                        contravariant.extend(field_indirect.contravariant.into_iter().map(project));
                    }
                }
                // TODO: recurse into other types
                _ => (),
            }
            deps.emit_output_ref(
                *task_key,
                IndirectPredicatesEncOutputRef {
                    covariant,
                    contravariant,
                },
            )?;
            Ok(((), ()))
        })
    }
}
