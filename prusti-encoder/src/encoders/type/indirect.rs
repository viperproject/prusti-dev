use prusti_rustc_interface::middle::ty::{self};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::Reify;

use super::rust_ty_predicates::RustTyPredicatesEnc;

pub struct IndirectPredicatesEnc;

#[derive(Clone)]
pub struct IndirectPredicatesEncOutputRef<'vir> {
    pub expr_pre: Vec<vir::ExprGen<'vir, vir::Expr<'vir>, vir::ExprKind<'vir>>>,
    pub expr_post: Vec<vir::ExprGen<'vir, vir::Expr<'vir>, vir::ExprKind<'vir>>>,
}

impl<'vir> task_encoder::OutputRefAny for IndirectPredicatesEncOutputRef<'vir> {}

impl TaskEncoder for IndirectPredicatesEnc {
    task_encoder::encoder_cache!(IndirectPredicatesEnc);

    type TaskDescription<'vir> = (ty::Ty<'vir>, ty::Region<'vir>);

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
            let self_ty_enc = deps.require_ref::<RustTyPredicatesEnc>(*ty)?;
            let mut expr_pre = Vec::new();
            let mut expr_post = Vec::new();
            match ty.kind() {
                ty::TyKind::Ref(ref_region, inner_ty, ty::Mutability::Mut) => {
                    let inner_ty_enc = deps.require_ref::<RustTyPredicatesEnc>(*inner_ty)?;
                    let deref_access = self_ty_enc.generic_predicate.expect_mutref().deref_func;
                    let inner_ty_enc_c = inner_ty_enc.clone();
                    if ref_region == proj_region {
                        expr_pre.push(vcx.mk_lazy_expr("ref_indirect", Box::new(move |vcx, self_expr| inner_ty_enc.ref_to_pred(
                            vcx,
                            deref_access.apply(vcx, [self_expr]),
                            None,
                        ).kind)));
                        expr_post.push(vcx.mk_lazy_expr("ref_indirect_post", Box::new(move |vcx, self_expr| inner_ty_enc_c.ref_to_pred(
                            vcx,
                            vcx.mk_old_expr(deref_access.apply(vcx, [self_expr])),
                            None,
                        ).kind)));
                    }
                    // TODO: is this correct??? do we always project into the inner type, regardless of region?
                    let inner_indirect = deps.require_ref::<IndirectPredicatesEnc>((*inner_ty, *proj_region))?;
                    expr_pre.extend(inner_indirect.expr_pre.into_iter()
                        .map(|inner_expr| vcx.mk_lazy_expr("ref_inner_indirect", Box::new(move |vcx, self_expr| inner_expr.reify(vcx, deref_access.apply(vcx, [self_expr])).kind))));
                    expr_post.extend(inner_indirect.expr_post.into_iter()
                        // TODO: where does the old go here?
                        .map(|inner_expr| vcx.mk_lazy_expr("ref_inner_indirect_post", Box::new(move |vcx, self_expr| inner_expr.reify(vcx, deref_access.apply(vcx, [self_expr])).kind))));
                }
                ty::TyKind::Tuple(params) => {
                    let field_accessors = self_ty_enc.generic_predicate.expect_structlike().ref_to_field_refs;
                    for (field_ty, accessor) in params.into_iter().zip(field_accessors) {
                        // TODO: tuple generics need to be passed to field accessors
                        // TODO: tuple fields need to be (snapshot) cast
                        let field_indirect = deps.require_ref::<IndirectPredicatesEnc>((field_ty, *proj_region))?;
                        expr_pre.extend(field_indirect.expr_pre.into_iter()
                            .map(|inner_expr| vcx.mk_lazy_expr("ref_inner_indirect", Box::new(move |vcx, self_expr| inner_expr.reify(vcx, accessor.apply(vcx, &[self_expr])).kind))));
                        expr_post.extend(field_indirect.expr_post.into_iter()
                            // TODO: where does the old go here?
                            .map(|inner_expr| vcx.mk_lazy_expr("ref_inner_indirect_post", Box::new(move |vcx, self_expr| inner_expr.reify(vcx, accessor.apply(vcx, &[self_expr])).kind))));
                    }
                }
                // TODO: recurse into other types
                _ => (),
            }
            deps.emit_output_ref(
                *task_key,
                IndirectPredicatesEncOutputRef {
                    expr_pre,
                    expr_post,
                },
            )?;
            Ok(((), ()))
        })
    }
}
