use prusti_rustc_interface::{
    middle::ty,
    abi,
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};

use crate::encoders::{lifted::{casters::{CastTypeImpure, CastTypePure}, rust_ty_cast::{GenericCasterImpure, GenericCasterPure, RustTyCastersEnc}, LiftedTyEncTask}, predicate::{PredicateEnc, PredicateEncDataEnum, PredicateEncDataImmRef, PredicateEncDataMutRef, PredicateEncDataStruct}, PredicateEncOutput, PredicateEncOutputRef};

use super::{
    lifted::{
        generic::LiftedGeneric,
        ty::{EncodeGenericsAsLifted, LiftedTy, LiftedTyEnc},
    },
    most_generic_ty::extract_type_params,
};

/// Encodes a type into the predicate representation. Takes an arbitrary Rust
/// `Ty` and provides a wrapper around the results of the `PredicateEnc` encoder.
/// This wrapper handles all the generic casts required (e.g. when fold/unfolding).
pub struct TyImpureEnc;

#[derive(Clone)]
pub struct TyImpureEncOutputRef<'vir> {
    /// The predicate output for the "most generic version" of the input type
    generic_predicate: PredicateEncOutputRef<'vir>,

    pub indirect_predicate: Option<(
        vir::ExprGenBool<'vir, vir::ExprRef<'vir>, vir::ExprKind<'vir>>,
        vir::ExprGenBool<'vir, vir::ExprRef<'vir>, vir::ExprKind<'vir>>,
    )>,

    /// The lifted representation of the input type, as a Viper value
    pub ty: LiftedTy<'vir, LiftedGeneric<'vir>>,

    pub f_ty: GenericCasterPure<'vir>,

    params: Vec<GenericCasterImpure<'vir>>,
}

pub struct TyImpureDataStruct<'a, 'vir> {
    params: &'a [GenericCasterImpure<'vir>],
    ty_args: Vec<vir::ExprTyVal<'vir>>,

    ref_to_pred: vir::PredicateIdn<'vir, (vir::Ref, vir::ManyTyVal)>,
    inner: Option<PredicateEncDataStruct<'vir>>,
}

pub struct TyImpureDataEnum<'vir> {
    inner: PredicateEncDataEnum<'vir>,
    ty_args: Vec<vir::ExprTyVal<'vir>>,
}

pub struct TyImpureDataImmRef<'vir> {
    inner: PredicateEncDataImmRef<'vir>,
    ty_args: Vec<vir::ExprTyVal<'vir>>,
}

pub struct TyImpureDataMutRef<'vir> {
    inner: PredicateEncDataMutRef<'vir>,
    ty_args: Vec<vir::ExprTyVal<'vir>>,
}

impl<'vir> TyImpureEncOutputRef<'vir> {
    /// Generates a call to `method_assign`, which asserts that the snapshot of
    /// `self_ref` is `self_new_snap`. Appropriate type arguments are used.
    pub fn apply_method_assign<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        self_ref: vir::ExprRef<'vir>,
        self_new_snap: vir::ExprSnap<'vir>,
    ) -> vir::Stmt<'vir> {
        assert_eq!(
            self.snapshot(),
            self_new_snap.ty(),
            "rhs of assignment does not have expected type"
        );
        vcx.alloc(vir::StmtData::new(vcx.alloc(
            (self.generic_predicate.method_assign)(
                self_ref,
                &self.ty.arg_exprs(vcx),
                self_new_snap,
            ),
        )))
    }

    /// The snapshot type.
    pub fn snapshot(&self) -> vir::TypeSnap<'vir> {
        self.generic_predicate.snapshot
    }

    /// Constructs the Viper predicate application expression.
    pub fn ref_to_pred<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        self_ref: vir::ExprRef<'vir>,
        perm: Option<vir::ExprPerm<'vir>>,
    ) -> vir::ExprBool<'vir> {
        vcx.mk_predicate_app_expr(self.ref_to_pred_app(vcx, self_ref, perm))
    }

    /// Constructs the Viper predicate application.
    pub fn ref_to_pred_app<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        self_ref: vir::ExprRef<'vir>,
        perm: Option<vir::ExprPerm<'vir>>,
    ) -> vir::PredicateApp<'vir> {
        (self.generic_predicate.ref_to_pred)(self_ref, &self.ref_to_ty_args(vcx))(perm)
    }

    /// Calls the predicate (heap) dependent snapshot construction function.
    pub fn ref_to_snap<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        self_ref: vir::ExprRef<'vir>,
    ) -> vir::ExprSnap<'vir> {
        let expr = (self.generic_predicate.ref_to_snap)(self_ref, &self.ref_to_ty_args(vcx));
        assert!(expr.ty() == self.snapshot());
        expr
    }

    /// Get the struct specifics (or enum variant if specified), panics if not a struct.
    pub fn expect_variant_opt(&self, vid: Option<abi::VariantIdx>) -> TyImpureDataStruct<'_, 'vir> {
        let ref_to_pred = self.generic_predicate.get_ref_to_pred(vid);
        let inner = self.generic_predicate.get_variant_opt(vid).copied();
        let ty_args = self.ref_to_ty_args(vir::with_vcx(|vcx| vcx));
        TyImpureDataStruct { ty_args, params: &self.params, ref_to_pred, inner }
    }

    /// Optionally get the enum specifics, `None` if not an enum. The inner
    /// option is a `None` if this is an empty enum (uninhabited).
    pub fn get_enumlike(&self) -> Option<Option<TyImpureDataEnum<'vir>>> {
        self.generic_predicate
            .get_enumlike()
            .map(|&inner| inner.map(|inner| TyImpureDataEnum {
                inner,
                ty_args: self.ref_to_ty_args(vir::with_vcx(|vcx| vcx)),
            }))
    }

    /// Get the immref specifics, panics if not immref.
    pub fn expect_immref(&self) -> TyImpureDataImmRef<'vir> {
        let inner = self.generic_predicate.expect_immref();
        let ty_args = self.ref_to_ty_args(vir::with_vcx(|vcx| vcx));
        TyImpureDataImmRef { inner, ty_args }
    }

    /// Get the mutref specifics, panics if not mutref.
    pub fn expect_mutref(&self) -> TyImpureDataMutRef<'vir> {
        let inner = self.generic_predicate.expect_mutref();
        let ty_args = self.ref_to_ty_args(vir::with_vcx(|vcx| vcx));
        TyImpureDataMutRef { inner, ty_args }
    }

    /// Constructs arguments for [`PredicateEncOutputRef::ref_to_pred`] and
    /// [`PredicateEncOutputRef::ref_to_snap`]. Takes as input a Ref representing
    /// the self, and the encoded Rust type (see [`LiftedTy`]). The arguments to the
    /// function are the type arguments of the lifted type.
    fn ref_to_ty_args<'tcx>(&self, vcx: &'vir vir::VirCtxt<'tcx>) -> Vec<vir::ExprTyVal<'vir>> {
        self.ty.arg_exprs(vcx)
    }
}

impl<'vir> TyImpureDataStruct<'_, 'vir> {
    /// Get the (Ref) address of a field.
    pub fn field<Curr, Next>(&self, field: abi::FieldIdx, self_ref: vir::ExprGenRef<'vir, Curr, Next>) -> vir::ExprGenRef<'vir, Curr, Next> {
        let ty_args = (&*self.ty_args) as *const [vir::ExprTyVal<'vir>] as *const [vir::ExprGenTyVal<'vir, Curr, Next>];
        // TODO: remove unsafe
        let ty_args = unsafe { &*ty_args };
        self.inner.expect("field of enum with no variant").ref_to_field_refs[field.index()].call()(self_ref, ty_args)
    }

    /// Fold the predicate (including generic casts).
    pub fn fold(
        &self,
        self_ref: vir::ExprRef<'vir>,
        perm: Option<vir::ExprPerm<'vir>>,
    ) -> impl Iterator<Item = vir::Stmt<'vir>> + '_ {
        vir::with_vcx(|vcx| {
            let to_gen = self.generic_fields(self_ref).filter_map(|(f_ref, param)| {
                param.cast_to_generic_if_necessary(vcx, f_ref)
            });

            let pred_app = self.ref_to_pred_app(self_ref, perm);
            let fold = vir::with_vcx(|vcx| vcx.mk_fold_stmt(pred_app));
            to_gen.chain([fold])
        })
    }

    /// Unfold the predicate (including generic casts).
    pub fn unfold(
        &self,
        self_ref: vir::ExprRef<'vir>,
        perm: Option<vir::ExprPerm<'vir>>,
    ) -> impl Iterator<Item = vir::Stmt<'vir>> + '_ {
        vir::with_vcx(|vcx| {
            let to_con = self.generic_fields(self_ref).filter_map(|(f_ref, param)| {
                param.cast_to_concrete_if_possible(vcx, f_ref)
            });

            let pred_app = self.ref_to_pred_app(self_ref, perm);
            let unfold = vir::with_vcx(|vcx| vcx.mk_unfold_stmt(pred_app));
            [unfold].into_iter().chain(to_con)
        })
    }

    fn generic_fields(&self, self_ref: vir::ExprRef<'vir>) -> impl Iterator<Item = (vir::ExprRef<'vir>, GenericCasterImpure<'vir>)> + '_ {
        self.inner.into_iter().flat_map(|inner| {
            assert_eq!(inner.ref_to_field_refs.len(), inner.snap_data.field_access.len());
            let fields = inner.ref_to_field_refs.iter().zip(inner.snap_data.field_access);
            fields.filter_map(|(f_ref, f)| f.generic_idx.map(|idx| (f_ref.call()(self_ref, &self.ty_args), self.params[idx as usize])))
        })
    }

    fn ref_to_pred_app(
        &self,
        self_ref: vir::ExprRef<'vir>,
        perm: Option<vir::ExprPerm<'vir>>,
    ) -> vir::PredicateApp<'vir> {
        (self.ref_to_pred)(self_ref, &self.ty_args)(perm)
    }
}

impl<'vir> TyImpureDataEnum<'vir> {
    pub fn discr(&self, self_ref: vir::ExprRef<'vir>) -> vir::ExprRef<'vir> {
        (self.inner.discr)(self_ref)
    }
}

impl<'vir> TyImpureDataImmRef<'vir> {
    pub fn deref(&self, self_ref: vir::ExprRef<'vir>) -> vir::ExprRef<'vir> {
        (self.inner.deref_func)(self_ref, &self.ty_args)
    }
}

impl<'vir> TyImpureDataMutRef<'vir> {
    pub fn deref(&self, self_ref: vir::ExprRef<'vir>) -> vir::ExprRef<'vir> {
        (self.inner.deref_func)(self_ref)
    }
}

impl<'vir> task_encoder::OutputRefAny for TyImpureEncOutputRef<'vir> {}

impl TaskEncoder for TyImpureEnc {
    task_encoder::encoder_cache!(TyImpureEnc);

    type TaskDescription<'vir> = ty::Ty<'vir>;

    type OutputRef<'vir> = TyImpureEncOutputRef<'vir>;
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
                let inner_ty_enc = deps.require_ref::<TyImpureEnc>(*inner_ty).unwrap();
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
            let ty = deps.require_local::<LiftedTyEnc<EncodeGenericsAsLifted>>(LiftedTyEncTask::Ty(*task_key))?;
            let f_ty = deps.require_local::<RustTyCastersEnc<CastTypePure>>(*task_key)?;
            let params = args
                        .iter()
                        .map(|arg| {
                            deps.require_local::<RustTyCastersEnc<CastTypeImpure>>(*arg)
                                .unwrap()
                        })
                        .collect();
            deps.emit_output_ref(
                *task_key,
                TyImpureEncOutputRef {
                    generic_predicate,
                    indirect_predicate: None,
                    ty,
                    f_ty,
                    params,
                },
            )?;
            Ok(((), ()))
        })
    }

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        PredicateEnc::emit_outputs(program)
    }
}
