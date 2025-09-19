use prusti_rustc_interface::middle::ty::{self};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, Reify};

use crate::encoders::ty::{
    RustTyDatas, data::StructData, generics::GParams, use_pure::UsePureTyDatas,
};

use super::{data::TySpecifics, use_impure::TyUseImpureEnc, use_pure::TyUsePureEnc};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IndirectKey {
    Early(ty::EarlyParamRegion),
    Late(ty::BoundRegionKind),
    Var(ty::RegionVid),
    Param(ty::ParamTy),
}

impl IndirectKey {
    pub fn from_generic_arg(ga: ty::GenericArg) -> Option<Self> {
        match ga.kind() {
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
            RegionKind::ReLateParam(_r) => None, // TODO: Some(IndirectKey::Late(r.bound_region)),
            RegionKind::ReVar(r) => Some(IndirectKey::Var(r)),
            RegionKind::RePlaceholder(..) | RegionKind::ReError(..) | RegionKind::ReErased => {
                unreachable!("{region:?}")
            }
            RegionKind::ReStatic => None,
        }
    }
}

pub struct IndirectPredicatesEnc;

type ExprInput<'vir> = vir::ExprSnap<'vir>;
type ExprOutput<'vir> = vir::ExprGenBool<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>;

#[derive(Debug, Clone, Default)]
pub struct IndirectPredicatesEncOutputRef<'vir> {
    pub covariant: Vec<ExprOutput<'vir>>,
    pub contravariant: Vec<ExprOutput<'vir>>,
}

impl<'vir> task_encoder::OutputRefAny for IndirectPredicatesEncOutputRef<'vir> {}

impl TaskEncoder for IndirectPredicatesEnc {
    task_encoder::encoder_cache!(IndirectPredicatesEnc);

    type TaskDescription<'vir> = (super::RustTyDecomposition<'vir>, IndirectKey);

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
            let (ty, proj_region) = task_key;
            let self_ty_enc = deps.require_dep::<TyUsePureEnc>(*ty)?;
            let mut output = IndirectPredicatesEncOutputRef::default();
            let combined = ty.ty.zip(self_ty_enc);
            match combined.specifics {
                // Optimisation: if there are no type arguments, there cannot be
                // anything behind a ref inside (except for 'static, which we
                // ignore for now). Plus it skips unsupported types if they
                // don't have lifetimes.
                _ if ty.args.args().is_empty() => (),
                TySpecifics::Primitive(_) | TySpecifics::ImmRef(_) => (),
                // TODO: it's not valid to have nothing for these. We should fix
                // this by using an opaque predicate to represent potential
                // indirect stuff. For example:
                // fn foo<'a, T: Trait<'a>>(x: T) -> &'a mut i32 { x.get() }
                // Here, `T` could be instantiated as `&'a mut i32` in which
                // case we would want a wand with `i32(result) --* opaque_behind_a(x)`.
                // This is why we should return `opaque_behind_a(x)` here.
                TySpecifics::Param(_) | TySpecifics::Opaque(_) => (),
                TySpecifics::MutRef((data, ref_domain)) => {
                    let inner_ty = data.decompose_normalize(ty.args);
                    let region = ty.args.args()[0].expect_region();
                    if IndirectKey::from_region(region)
                        .is_some_and(|indirect| &indirect == proj_region)
                    {
                        let inner_ty_enc = deps.require_dep::<TyUseImpureEnc>(inner_ty)?;
                        output.covariant.push(vcx.mk_lazy_expr(
                            "ref_indirect",
                            vir::TYPE_BOOL,
                            Box::new(move |vcx, self_expr| {
                                inner_ty_enc
                                    .ref_to_pred(
                                        vcx,
                                        ref_domain.deref_access(self_expr.downcast_ty()),
                                        None,
                                    )
                                    .kind
                            }),
                        ));
                    }
                    // TODO: is this correct??? do we always project into the inner type, regardless of region?
                    let inner_indirect =
                        deps.require_dep::<IndirectPredicatesEnc>((inner_ty, *proj_region))?;
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
                                            ref_domain.value_access(self_expr.downcast_ty()),
                                        )
                                        .kind
                                }),
                            )
                        })
                        .collect::<Vec<_>>();
                    output.covariant.extend(inner.clone());
                    output.contravariant.extend(inner);
                }
                TySpecifics::StructLike(data) => {
                    output = Self::indirect_structlike(deps, data, ty.ty.params, *proj_region)?.1;
                }
                TySpecifics::EnumLike(data) => {
                    let variants = data.variants.into_iter().map(|variant| {
                        Ok((
                            variant.1.discr,
                            Self::indirect_structlike(
                                deps,
                                variant.inner,
                                ty.ty.params,
                                *proj_region,
                            )?
                            .1,
                        ))
                    });
                    let enum_data = data.data.1;
                    let (covariant, contravariant) = vir::with_vcx(move |vcx| {
                        let discr_snap = vcx.mk_lazy_expr(
                            "enum_discr_indirect",
                            enum_data.discr_ty,
                            Box::new(move |_vcx, self_expr: vir::ExprGenSnap<_, _>| {
                                (enum_data.snap_to_discr_snap)(self_expr.downcast_ty()).kind
                            }),
                        );
                        variants.fold(
                            Ok((vcx.mk_bool::<true>().lazy(), vcx.mk_bool::<true>().lazy())),
                            |acc, data| {
                                let (covariant, contravariant) = acc?;
                                let (discr, data) = data?;
                                let (covar, contra) = (
                                    vcx.mk_conj(&data.covariant),
                                    vcx.mk_conj(&data.contravariant),
                                );
                                let discr_eq = vcx.mk_eq_expr(discr_snap, discr.lazy());
                                Ok((
                                    vcx.mk_ternary_expr(discr_eq, covar, covariant),
                                    vcx.mk_ternary_expr(discr_eq, contra, contravariant),
                                ))
                            },
                        )
                    })?;
                    output.covariant.push(covariant);
                    output.contravariant.push(contravariant);
                }
            }
            Ok(((), output))
        })
    }
}

impl IndirectPredicatesEnc {
    fn indirect_structlike<'vir>(
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        data: StructData<'vir, (RustTyDatas, UsePureTyDatas)>,
        params: GParams<'vir>,
        proj_region: IndirectKey,
    ) -> EncodeFullResult<'vir, Self> {
        let mut output = IndirectPredicatesEncOutputRef::default();
        let _ = vir::with_vcx(|vcx| {
            for (field_ty, accessor) in data.fields {
                let project = |inner_expr: ExprOutput<'vir>| {
                    vcx.mk_lazy_expr(
                        "ref_inner_indirect",
                        vir::TYPE_BOOL,
                        Box::new(move |vcx, self_expr: vir::ExprGenSnap<_, _>| {
                            inner_expr
                                .reify(vcx, accessor.read(self_expr.downcast_ty()))
                                .kind
                        }),
                    )
                };

                // TODO: invalid recursion here if the defined struct is
                // recursive!
                let field_ty = field_ty.decompose(params);
                let field_indirect =
                    deps.require_dep::<IndirectPredicatesEnc>((field_ty, proj_region))?;
                output
                    .covariant
                    .extend(field_indirect.covariant.into_iter().map(project));
                output
                    .contravariant
                    .extend(field_indirect.contravariant.into_iter().map(project));
            }
            Ok(())
        })?;
        Ok(((), output))
    }
}
