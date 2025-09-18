use prusti_rustc_interface::middle::ty::{self};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, Reify};

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

#[derive(Clone)]
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
        deps.emit_output_ref(
            *task_key,
            (),
        )?;
        vir::with_vcx(|vcx| {
            let (ty, proj_region) = task_key;
            let self_ty_enc = deps.require_dep::<TyUsePureEnc>(*ty)?;
            let mut covariant = Vec::<ExprOutput<'vir>>::new();
            let mut contravariant = Vec::<ExprOutput<'vir>>::new();
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
                        covariant.push(vcx.mk_lazy_expr(
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
                                            ref_domain.value_access(self_expr.downcast_ty())
                                        )
                                        .kind
                                }),
                            )
                        })
                        .collect::<Vec<_>>();
                    covariant.extend(inner.clone());
                    contravariant.extend(inner);
                }
                TySpecifics::StructLike(data) => {
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
                        let field_ty = field_ty.decompose(ty.ty.params);
                        let field_indirect =
                            deps.require_dep::<IndirectPredicatesEnc>((field_ty, *proj_region))?;
                        covariant.extend(field_indirect.covariant.into_iter().map(project));
                        contravariant.extend(field_indirect.contravariant.into_iter().map(project));
                    }
                }
                TySpecifics::EnumLike(_data) => todo!(),
            }
            Ok(((), IndirectPredicatesEncOutputRef {
                covariant,
                contravariant,
            }))
        })
    }
}
