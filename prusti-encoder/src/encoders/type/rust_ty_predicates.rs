use prusti_rustc_interface::middle::ty::{self};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};

use crate::encoders::{PredicateEnc, PredicateEncOutputRef};

use super::{
    lifted::{
        generic::LiftedGeneric,
        ty::{EncodeGenericsAsLifted, LiftedTy, LiftedTyEnc},
    },
    most_generic_ty::extract_type_params,
};

pub struct RustTyPredicatesEnc;

#[derive(Clone)]
pub struct RustTyPredicatesEncOutputRef<'vir> {
    /// The predicate output for the "most generic version" of the input type
    pub generic_predicate: PredicateEncOutputRef<'vir>,

    pub indirect_predicate: Option<(
        vir::ExprGen<'vir, vir::Expr<'vir>, vir::ExprKind<'vir>>,
        vir::ExprGen<'vir, vir::Expr<'vir>, vir::ExprKind<'vir>>,
    )>,

    /// The lifted representation of the input type, as a Viper value
    pub ty: LiftedTy<'vir, LiftedGeneric<'vir>>,
}

impl<'vir> RustTyPredicatesEncOutputRef<'vir> {
    /// Generates a call to `method_assign`, which asserts that the snapshot of
    /// `self_ref` is `self_new_snap`. Appropriate type arguments are used.
    pub fn apply_method_assign<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        self_ref: vir::Expr<'vir>,
        self_new_snap: vir::Expr<'vir>,
    ) -> vir::Stmt<'vir> {
        //assert_eq!(self_ref.ty(), &TypeData::Ref);
        assert_eq!(
            self.snapshot(),
            self_new_snap.ty(),
            "rhs of assignment does not have expected type"
        );
        let mut args = vec![self_ref];
        args.extend(self.ty.arg_exprs(vcx));
        args.push(self_new_snap);
        vcx.alloc(vir::StmtData::new(
            vcx.alloc(self.generic_predicate.method_assign.apply(vcx, &args)),
        ))
    }

    pub fn snapshot(&self) -> vir::Type<'vir> {
        self.generic_predicate.snapshot
    }

    pub fn ref_to_pred<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        self_ref: vir::Expr<'vir>,
        perm: Option<vir::Expr<'vir>>,
    ) -> vir::Expr<'vir> {
        vcx.mk_predicate_app_expr(self.ref_to_pred_app(vcx, self_ref, perm))
    }

    pub fn ref_to_pred_app<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        self_ref: vir::Expr<'vir>,
        perm: Option<vir::Expr<'vir>>,
    ) -> vir::PredicateApp<'vir> {
        self.generic_predicate
            .ref_to_pred
            .apply(vcx, self.ref_to_args(vcx, self_ref), perm)
    }

    pub fn ref_to_snap<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        self_ref: vir::Expr<'vir>,
    ) -> vir::Expr<'vir> {
        let expr = self
            .generic_predicate
            .ref_to_snap
            .apply(vcx, self.ref_to_args(vcx, self_ref));
        assert!(expr.ty() == self.snapshot());
        expr
    }

    pub fn ref_to_indirect_pred<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        self_ref: vir::Expr<'vir>,
        _perm: Option<vir::Expr<'vir>>,
        // TODO: make this a function of a lifetime being projected?
        // lifetime: ty::Region<'tcx>,
    ) -> Option<(vir::Expr<'vir>, vir::Expr<'vir>)> {
        use vir::Reify;
        self.indirect_predicate
            .map(|(pre, post)| (pre.reify(vcx, self_ref), post.reify(vcx, self_ref)))
        //.map(|pred| vcx.mk_predicate_app_expr(pred.apply(vcx, self.ref_to_args(vcx, self_ref), perm)))
    }

    /// Arguments to `ref_to_pred` and `ref_to_snap`.
    pub fn ref_to_args<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        self_ref: vir::Expr<'vir>,
    ) -> &'vir [vir::Expr<'vir>] {
        self.generic_predicate.ref_to_args(vcx, self.ty, self_ref)
    }
}

impl<'vir> task_encoder::OutputRefAny for RustTyPredicatesEncOutputRef<'vir> {}

impl TaskEncoder for RustTyPredicatesEnc {
    task_encoder::encoder_cache!(RustTyPredicatesEnc);

    type TaskDescription<'vir> = ty::Ty<'vir>;

    type OutputRef<'vir> = RustTyPredicatesEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = ();

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let (generic_ty, args) = extract_type_params(vcx.tcx(), *task_key);
            let generic_predicate = deps.require_ref::<PredicateEnc>(generic_ty)?;
            /*
            let indirect_predicate = if let ty::TyKind::Ref(_, inner_ty, _) = task_key.kind() {
                let inner_ty_enc = deps.require_ref::<RustTyPredicatesEnc>(*inner_ty).unwrap();
                let deref_access = generic_predicate.expect_ref().deref_func;
                let inner_ty_enc_c = inner_ty_enc.clone();
                Some((
                    vcx.mk_lazy_expr("ref_indirect", Box::new(move |vcx, self_expr| inner_ty_enc.ref_to_pred(
                        vcx,
                        deref_access.apply(vcx, [self_expr]),
                        None,
                    ).kind)),
                    vcx.mk_lazy_expr("ref_indirect_post", Box::new(move |vcx, self_expr| inner_ty_enc_c.ref_to_pred(
                        vcx,
                        vcx.mk_old_expr(deref_access.apply(vcx, [self_expr])),
                        None,
                    ).kind)),
                ))
            } else {
                None
            };
            */
            let ty = deps.require_local::<LiftedTyEnc<EncodeGenericsAsLifted>>(*task_key)?;
            deps.emit_output_ref(
                *task_key,
                RustTyPredicatesEncOutputRef {
                    generic_predicate,
                    indirect_predicate: None,
                    ty,
                },
            )?;
            for arg in args {
                deps.require_ref::<RustTyPredicatesEnc>(arg)?;
            }
            Ok(((), ()))
        })
    }

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }
}
