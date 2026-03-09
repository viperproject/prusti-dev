use pcg::borrow_pcg::region_projection::{LifetimeProjection, PcgRegion};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, Reify};

use crate::encoders::{TyUseImpureEnc, ty::RustTyDecomposition};

use super::{data::TySpecifics, use_pure::TyUsePureEnc};

pub struct IndirectPredicatesEnc;

type ExprInput<'vir> = vir::ExprSnap<'vir>;
type ExprOutput<'vir> = vir::ExprGenBool<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>;

#[derive(Clone)]
pub struct IndirectPredicatesEncOutputRef<'vir> {
    pub predicate_applications: Vec<ExprOutput<'vir>>,
}

impl<'vir> IndirectPredicatesEncOutputRef<'vir> {
    pub fn new(predicate_applications: Vec<ExprOutput<'vir>>) -> Self {
        Self {
            predicate_applications,
        }
    }
}

impl<'vir> task_encoder::OutputRefAny for IndirectPredicatesEncOutputRef<'vir> {}

impl TaskEncoder for IndirectPredicatesEnc {
    task_encoder::encoder_cache!(IndirectPredicatesEnc);

    type TaskDescription<'vir> = LifetimeProjection<'vir, RustTyDecomposition<'vir>>;

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
            let ty = task_key.base();
            let self_ty_enc = deps.require_dep::<TyUsePureEnc>(ty)?;
            let combined = ty.ty.zip(self_ty_enc);
            let mut predicate_applications = vec![];
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
                TySpecifics::Param(_) | TySpecifics::Opaque(_) | TySpecifics::ArrayLike(_) => (),
                TySpecifics::MutRef((data, ref_domain)) => {
                    assert_eq!(ty.args.args().len(), 2);
                    let inner_ty = data.decompose_context(ty.ty.params, ty.args);
                    let inner_impure = deps.require_dep::<TyUseImpureEnc>(inner_ty)?;
                    let ref_region = PcgRegion::from(ty.args.args()[0].expect_region());
                    let task_region = task_key.region(());
                    if ref_region == task_region {
                        predicate_applications.push(vcx.mk_lazy_expr(
                            "ref_indirect",
                            vir::TYPE_BOOL,
                            Box::new(move |vcx, self_expr: vir::ExprSnap<'vir>| {
                                let addr = ref_domain.deref_access(self_expr.downcast_ty());
                                inner_impure.ref_to_pred(vcx, addr, None).kind
                            }),
                        ));
                    }
                    if let Some(new_projection) =
                        LifetimeProjection::new(inner_ty, task_key.region(()), None, ())
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
                    }
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
                        let field_ty = field_ty.decompose_context(ty.ty.params, ty.args);
                        let new_projection =
                            LifetimeProjection::new(field_ty, task_key.region(()), None, ())
                                .unwrap();
                        let field_indirect =
                            deps.require_dep::<IndirectPredicatesEnc>(new_projection)?;
                        predicate_applications.extend(
                            field_indirect
                                .predicate_applications
                                .into_iter()
                                .map(project),
                        );
                    }
                }
                // TODO: recurse into other types
                _ => {}
            };
            Ok((
                (),
                IndirectPredicatesEncOutputRef::new(predicate_applications),
            ))
        })
    }
}
