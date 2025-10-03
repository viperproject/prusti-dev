use prusti_rustc_interface::abi;
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::PredicateIdn;

use crate::encoders::{
    Impure,
    ty::{
        LazyRustTy, RustTyDatas,
        generics::{GArgs, GArgsCastEnc, GArgsTyEnc, GParams},
    },
};

use super::{
    TyUseEnc, UseTyDatas,
    data::*,
    generics::{GArgCaster, GArgsTy},
    impure::{ImpureTyDatas, TyImpureEnc},
};

pub(super) type UseImpureTyDatas = UseTyDatas<Impure>;

type FieldCaster<'vir> = GArgCaster<'vir, Impure>;

impl<'vir> TyDatas<'vir> for UseImpureTyDatas {
    type TyData = TyUseImpureData<'vir>;
    type PrimitiveData = ();
    type ImmRefData = TyUseImpureImmRef<'vir>;
    type MutRefData = TyUseImpureMutRef<'vir>;
    type FieldData = TyUseImpureField<'vir>;
    type StructData = TyUseImpureStructData<'vir>;
    type VariantData = ();
    type EnumData = TyUseImpureEnumData<'vir>;
}

pub type TyUseImpure<'vir> = Ty<'vir, UseImpureTyDatas>;

pub type TyUseImpureStruct<'vir> = StructData<'vir, UseImpureTyDatas>;
pub type TyUseImpureEnum<'vir> = EnumData<'vir, UseImpureTyDatas>;

#[derive(Debug, Clone, Copy)]
pub struct TyUseImpureData<'vir> {
    args: GArgsTy<'vir>,
    impure: <ImpureTyDatas as TyDatas<'vir>>::TyData,
}

#[derive(Debug, Clone, Copy)]
pub struct TyUseImpureImmRef<'vir> {
    #[allow(dead_code)]
    caster: FieldCaster<'vir>,
    #[allow(dead_code)]
    args: GArgsTy<'vir>,
    #[allow(dead_code)]
    impure: <ImpureTyDatas as TyDatas<'vir>>::ImmRefData,
}

#[derive(Debug, Clone, Copy)]
pub struct TyUseImpureMutRef<'vir> {
    #[allow(dead_code)]
    caster: FieldCaster<'vir>,
    args: GArgsTy<'vir>,
    impure: <ImpureTyDatas as TyDatas<'vir>>::MutRefData,
}

#[derive(Debug, Clone, Copy)]
pub struct TyUseImpureStructData<'vir> {
    args: GArgsTy<'vir>,
    ref_to_pred: PredicateIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>,
    #[allow(dead_code)]
    impure: <ImpureTyDatas as TyDatas<'vir>>::StructData,
}

#[derive(Debug, Clone, Copy)]
pub struct TyUseImpureField<'vir> {
    caster: FieldCaster<'vir>,
    args: GArgsTy<'vir>,
    impure: <ImpureTyDatas as TyDatas<'vir>>::FieldData,
}

#[derive(Debug, Clone, Copy)]
pub struct TyUseImpureEnumData<'vir> {
    #[allow(dead_code)]
    args: GArgsTy<'vir>,
    impure: <ImpureTyDatas as TyDatas<'vir>>::EnumData,
}

/// Encodes a type into the predicate representation. Takes an arbitrary Rust
/// `Ty` and provides a wrapper around the results of the `TyImpureEnc` encoder.
/// This wrapper handles all the generic casts required (e.g. when fold/unfolding).
pub type TyUseImpureEnc = TyUseEnc<Impure>;

impl TaskEncoder for TyUseImpureEnc {
    task_encoder::encoder_cache!(TyUseImpureEnc);

    type TaskDescription<'vir> = super::RustTyDecomposition<'vir>;

    type OutputFullDependency<'vir> = TyUseImpure<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;

        let ty_impure = deps.require_dep::<TyImpureEnc>(task_key.ty)?;
        let mut walker = TyUseImpureWalker::new(deps, task_key.args);
        let ty_use_impure = walker.encode_ty(task_key.ty.zip(ty_impure));
        Ok(((), ty_use_impure.alloc()))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        TyImpureEnc::emit_outputs(program)
    }
}

struct TyUseImpureWalker<'a, 'vir> {
    deps: &'a mut TaskEncoderDependencies<'vir, TyUseImpureEnc>,
    args_t: GArgsTy<'vir>,
    args: GArgs<'vir>,
}

impl<'a, 'vir> TyUseImpureWalker<'a, 'vir> {
    fn new(deps: &'a mut TaskEncoderDependencies<'vir, TyUseImpureEnc>, args: GArgs<'vir>) -> Self {
        let args_t = deps.require_dep::<GArgsTyEnc>(args).unwrap();
        Self { deps, args_t, args }
    }

    fn encode_ty(
        &mut self,
        ty: TyData<'vir, (RustTyDatas, ImpureTyDatas)>,
    ) -> TyData<'vir, UseImpureTyDatas> {
        let specifics = match &ty.specifics {
            TySpecifics::Param(..) => TySpecifics::mk_param(()),
            TySpecifics::Opaque(..) => TySpecifics::mk_opaque(()),
            TySpecifics::Primitive(..) => TySpecifics::mk_primitive(()),
            TySpecifics::ImmRef(data) => {
                let caster = self.encode_normalized(*data.0, ty.0.params);
                TySpecifics::mk_immref(TyUseImpureImmRef {
                    caster,
                    args: self.args_t,
                    impure: *data.1,
                })
            }
            TySpecifics::MutRef(data) => {
                let caster = self.encode_normalized(*data.0, ty.0.params);
                TySpecifics::mk_mutref(TyUseImpureMutRef {
                    caster,
                    args: self.args_t,
                    impure: *data.1,
                })
            }
            TySpecifics::StructLike(data) => {
                TySpecifics::StructLike(self.encode_structlike(data, ty.1.ref_to_pred, ty.0.params))
            }
            TySpecifics::EnumLike(data) => {
                TySpecifics::EnumLike(self.encode_enumlike(data, ty.0.params))
            }
        };
        let data = TyUseImpureData {
            args: self.args_t,
            impure: *ty.1,
        };
        TyData::new(data, ty.inhabited, specifics)
    }

    fn encode_normalized(
        &mut self,
        inner: LazyRustTy<'vir>,
        params: GParams<'vir>,
    ) -> FieldCaster<'vir> {
        let normalized = inner.decompose_compare_normalize(params, self.args);
        self.deps
            .require_dep::<GArgsCastEnc<Impure>>(normalized)
            .unwrap()
    }

    fn encode_structlike(
        &mut self,
        data: &StructData<'vir, (RustTyDatas, ImpureTyDatas)>,
        ref_to_pred: PredicateIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>,
        params: GParams<'vir>,
    ) -> StructData<'vir, UseImpureTyDatas> {
        let fields = data
            .fields
            .iter()
            .map(|field| {
                let caster = self.encode_normalized(field.0.ty(), params);
                TyUseImpureField {
                    caster,
                    args: self.args_t,
                    impure: *field.1,
                }
            })
            .collect::<Vec<_>>();
        let inhabited = data.inhabited;
        let data = TyUseImpureStructData {
            args: self.args_t,
            ref_to_pred,
            impure: *data.1,
        };
        StructData::new(data, inhabited, fields)
    }

    fn encode_enumlike(
        &mut self,
        data: &EnumData<'vir, (RustTyDatas, ImpureTyDatas)>,
        params: GParams<'vir>,
    ) -> EnumData<'vir, UseImpureTyDatas> {
        let variants = data
            .variants
            .iter()
            .map(|variant| {
                let structlike =
                    self.encode_structlike(&variant.inner, variant.1.predicate, params);
                VariantData::new((), variant.inhabited, structlike)
            })
            .collect::<Vec<_>>();
        let inhabited = data.inhabited;
        let data = TyUseImpureEnumData {
            args: self.args_t,
            impure: *data.1,
        };
        EnumData::new(data, inhabited, variants)
    }
}

impl<'vir> TyUseImpureData<'vir> {
    /// Generates a call to `method_assign`, which asserts that the snapshot of
    /// `self_ref` is `self_new_snap`. Appropriate type arguments are used.
    pub fn apply_method_assign<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        self_ref: vir::ExprRef<'vir>,
        self_new_snap: vir::ExprSnap<'vir>,
    ) -> vir::Stmt<'vir> {
        vcx.alloc(vir::StmtData::new(vcx.alloc((self.impure.method_assign)(
            self_ref,
            self.args.get_ty(),
            self.args.get_const(),
            self_new_snap,
        ))))
    }

    /// Constructs the Viper predicate application expression.
    pub fn ref_to_pred<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        self_ref: vir::ExprRef<'vir>,
        perm: Option<vir::ExprPerm<'vir>>,
    ) -> vir::ExprBool<'vir> {
        if self.impure.inhabited {
            vcx.mk_predicate_app_expr(self.ref_to_pred_app(self_ref, perm))
        } else {
            vcx.mk_bool::<false>()
        }
    }

    /// Constructs the Viper predicate application.
    pub fn ref_to_pred_app(
        &self,
        self_ref: vir::ExprRef<'vir>,
        perm: Option<vir::ExprPerm<'vir>>,
    ) -> vir::PredicateApp<'vir> {
        (self.impure.ref_to_pred)(self_ref, self.args.get_ty(), self.args.get_const())(perm)
    }

    /// Calls the predicate (heap) dependent snapshot construction function.
    pub fn ref_to_snap(&self, self_ref: vir::ExprRef<'vir>) -> vir::ExprSnap<'vir> {
        (self.impure.ref_to_snap)(self_ref, self.args.get_ty(), self.args.get_const())
    }

    pub fn snapshot(&self) -> vir::TypeSnap<'vir> {
        self.impure.ref_to_snap.result()
    }
}

impl<'vir> TyData<'vir, UseImpureTyDatas> {
    /// Fold the predicate (including generic casts).
    pub fn fold(
        &self,
        variant: Option<abi::VariantIdx>,
        self_ref: vir::ExprRef<'vir>,
        perm: Option<vir::ExprPerm<'vir>>,
    ) -> Vec<vir::Stmt<'vir>> {
        if let Some(variant) = variant {
            return self
                .expect_variant(variant)
                .inner
                .fold(self_ref, perm)
                .collect();
        };
        match &self.specifics {
            TySpecifics::Param(_) | TySpecifics::Primitive(_) => unreachable!(),
            TySpecifics::Opaque(_) => panic!("cannot fold opaque type"),
            TySpecifics::ImmRef(..) => Vec::new(),
            TySpecifics::MutRef(data) => data.fold(self_ref).into_iter().collect(),
            TySpecifics::StructLike(data) => data.fold(self_ref, perm).collect(),
            TySpecifics::EnumLike(..) => {
                let pred_app = self.ref_to_pred_app(self_ref, perm);
                vec![vir::with_vcx(|vcx| vcx.mk_fold_stmt(pred_app))]
            }
        }
    }

    /// Unfold the predicate (including generic casts).
    pub fn unfold(
        &self,
        variant: Option<abi::VariantIdx>,
        self_ref: vir::ExprRef<'vir>,
        perm: Option<vir::ExprPerm<'vir>>,
    ) -> Vec<vir::Stmt<'vir>> {
        if let Some(variant) = variant {
            return self
                .expect_variant(variant)
                .inner
                .unfold(self_ref, perm)
                .collect();
        };
        match &self.specifics {
            TySpecifics::Param(_) | TySpecifics::Primitive(_) => unreachable!(),
            TySpecifics::Opaque(_) => panic!("cannot unfold opaque type"),
            TySpecifics::ImmRef(..) => Vec::new(),
            TySpecifics::MutRef(data) => data.unfold(self_ref).into_iter().collect(),
            TySpecifics::StructLike(data) => data.unfold(self_ref, perm).collect(),
            TySpecifics::EnumLike(..) => {
                let pred_app = self.ref_to_pred_app(self_ref, perm);
                vec![vir::with_vcx(|vcx| vcx.mk_unfold_stmt(pred_app))]
            }
        }
    }
}

impl<'vir> TyUseImpureStruct<'vir> {
    fn ref_to_pred_app(
        &self,
        self_ref: vir::ExprRef<'vir>,
        perm: Option<vir::ExprPerm<'vir>>,
    ) -> vir::PredicateApp<'vir> {
        (self.ref_to_pred)(self_ref, self.args.get_ty(), self.args.get_const())(perm)
    }

    /// Fold the predicate (including generic casts).
    fn fold(
        &self,
        self_ref: vir::ExprRef<'vir>,
        perm: Option<vir::ExprPerm<'vir>>,
    ) -> impl Iterator<Item = vir::Stmt<'vir>> + '_ {
        let pred_app = self.ref_to_pred_app(self_ref, perm);
        let fold = vir::with_vcx(|vcx| vcx.mk_fold_stmt(pred_app));
        self.cast_to_callee_ctx(self_ref).chain([fold])
    }

    /// Unfold the predicate (including generic casts).
    fn unfold(
        &self,
        self_ref: vir::ExprRef<'vir>,
        perm: Option<vir::ExprPerm<'vir>>,
    ) -> impl Iterator<Item = vir::Stmt<'vir>> + '_ {
        let pred_app = self.ref_to_pred_app(self_ref, perm);
        let unfold = vir::with_vcx(|vcx| vcx.mk_unfold_stmt(pred_app));
        [unfold]
            .into_iter()
            .chain(self.cast_to_caller_ctx(self_ref))
    }

    fn cast_to_caller_ctx(
        &self,
        self_ref: vir::ExprRef<'vir>,
    ) -> impl Iterator<Item = vir::Stmt<'vir>> {
        self.fields
            .iter()
            .filter_map(|f| f.cast_to_caller_ctx(self_ref))
    }

    fn cast_to_callee_ctx(
        &self,
        self_ref: vir::ExprRef<'vir>,
    ) -> impl Iterator<Item = vir::Stmt<'vir>> {
        self.fields
            .iter()
            .filter_map(|f| f.cast_to_callee_ctx(self_ref))
    }
}

impl<'vir> TyUseImpureField<'vir> {
    /// Get the (Ref) address of a field.
    pub fn field_ref<Curr, Next>(
        &self,
        self_ref: vir::ExprGenRef<'vir, Curr, Next>,
    ) -> vir::ExprGenRef<'vir, Curr, Next> {
        self.impure.ref_to_field_ref.call()(self_ref, self.args.get_ty(), self.args.get_const())
    }

    fn cast_to_caller_ctx(&self, self_ref: vir::ExprRef<'vir>) -> Option<vir::Stmt<'vir>> {
        self.caster.cast_to_caller_ctx(self.field_ref(self_ref))
    }

    fn cast_to_callee_ctx(&self, self_ref: vir::ExprRef<'vir>) -> Option<vir::Stmt<'vir>> {
        self.caster.cast_to_callee_ctx(self.field_ref(self_ref))
    }
}

impl<'vir> TyUseImpureEnum<'vir> {
    pub fn discr(&self, self_ref: vir::ExprRef<'vir>) -> vir::ExprRef<'vir> {
        (self.impure.discr)(self_ref)
    }

    pub fn discr_ty(&self) -> TyUseImpure<'vir> {
        self.impure.discr_ty
    }
}

impl<'vir> TyUseImpureImmRef<'vir> {}

impl<'vir> TyUseImpureMutRef<'vir> {
    pub fn deref(&self, self_ref: vir::ExprRef<'vir>) -> vir::ExprRef<'vir> {
        (self.impure.deref_func)(self_ref, self.args.get_ty(), self.args.get_const())
    }

    fn fold(&self, _self_ref: vir::ExprRef<'vir>) -> Option<vir::Stmt<'vir>> {
        // TODO: should the deref of a mut ref be generic or not?
        // self.caster.cast_to_callee_ctx(self.deref(self_ref))
        None
    }

    fn unfold(&self, _self_ref: vir::ExprRef<'vir>) -> Option<vir::Stmt<'vir>> {
        // self.caster.cast_to_caller_ctx(self.deref(self_ref))
        None
    }
}
