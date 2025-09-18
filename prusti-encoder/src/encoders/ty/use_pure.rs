use task_encoder::{EncodeFullResult, TaskEncoder};
use vir::{with_vcx, CastType, FunctionIdn};

use prusti_rustc_interface::{
    middle::ty,
};

use crate::encoders::{ty::{generics::{GArgs, GArgsCastEnc, GArgsTyEnc, GParams}, LazyRustTy, RustTy, RustTyDatas}, Pure};

use super::{
    generics::{GArgCaster, GArgsTy},
    pure::{PureTyDatas, TyPureRef, TyPureEnc},
    data::*,
    TyUseEnc, UseTyDatas,
};

pub(super) type UsePureTyDatas = UseTyDatas<Pure>;

type FieldCaster<'vir> = GArgCaster<'vir, Pure>;

impl<'vir> TyDatas<'vir> for UsePureTyDatas {
    type TyData = TyUsePureRef<'vir>;
    type OpaqueData = <PureTyDatas as TyDatas<'vir>>::OpaqueData;
    type ParamData = <PureTyDatas as TyDatas<'vir>>::ParamData;
    type PrimitiveData = <PureTyDatas as TyDatas<'vir>>::PrimitiveData;
    type ImmRefData = TyUsePureImmRef<'vir>;
    type MutRefData = TyUsePureMutRef<'vir>;
    type FieldData = TyUsePureField<'vir>;
    type StructData = TyUsePureStructData<'vir>;
    type VariantData = <PureTyDatas as TyDatas<'vir>>::VariantData;
    type EnumData = <PureTyDatas as TyDatas<'vir>>::EnumData;
}

pub type TyUsePure<'vir> = Ty<'vir, UsePureTyDatas>;
pub type TyUsePureData<'vir> = TyData<'vir, UsePureTyDatas>;
pub type TyUsePureStruct<'vir> = StructData<'vir, UsePureTyDatas>;
pub type TyUsePureEnum<'vir> = EnumData<'vir, UsePureTyDatas>;

#[derive(Debug, Clone, Copy)]
pub struct TyUsePureImmRef<'vir> {
    caster: FieldCaster<'vir>,
    pure: <PureTyDatas as TyDatas<'vir>>::ImmRefData,
}

#[derive(Debug, Clone, Copy)]
pub struct TyUsePureMutRef<'vir> {
    caster: FieldCaster<'vir>,
    pure: <PureTyDatas as TyDatas<'vir>>::MutRefData,
}

#[derive(Debug, Clone, Copy)]
pub struct TyUsePureField<'vir> {
    caster: FieldCaster<'vir>,
    pure: <PureTyDatas as TyDatas<'vir>>::FieldData,
}

#[derive(Debug, Clone, Copy)]
pub struct TyUsePureStructData<'vir> {
    args: GArgsTy<'vir>,
    pure: <PureTyDatas as TyDatas<'vir>>::StructData,
}

/// Encodes a type into the snapshot representation. Takes an arbitrary Rust
/// `Ty` and provides a wrapper around the results of the `DomainEnc` encoder.
/// This wrapper handles all the generic casts required.
pub type TyUsePureEnc = TyUseEnc<Pure>;

#[derive(Debug, Clone, Copy)]
pub struct TyUsePureRef<'vir> {
    pub snapshot: vir::TypeSnap<'vir>,
    args: GArgsTy<'vir>,
    ty_pure_ref: TyPureRef<'vir>,
}

impl<'vir> task_encoder::OutputRefAny for TyUsePureRef<'vir> {}

impl TaskEncoder for TyUsePureEnc {
    task_encoder::encoder_cache!(TyUsePureEnc);

    type TaskDescription<'vir> = super::RustTyDecomposition<'vir>;

    type OutputRef<'vir> = TyUsePureRef<'vir>;
    type OutputFullDependency<'vir> = TyUsePure<'vir>;

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type EncodingError = ();

    const ENCODER_NAME: &'static str = "pure type encoder";

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let ty_pure_ref = deps.require_ref::<TyPureEnc>(task_key.ty)?;
        let args = deps.require_dep::<GArgsTyEnc>(task_key.args)?;
        let snapshot = (ty_pure_ref.domain)();
        let inner = TyUsePureRef { args, snapshot, ty_pure_ref };
        deps.emit_output_ref(*task_key, inner)?;

        let ty_pure = deps.require_dep::<TyPureEnc>(task_key.ty)?;
        let ty = task_key.ty.zip(ty_pure);
        let mut walker = TyUsePureWalker::new(deps, task_key.args);
        let specifics = walker.encode_ty(ty);
        let ty_use_pure = TyData::new(inner, specifics);
        Ok(((), ty_use_pure.alloc()))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        TyPureEnc::emit_outputs(program)
    }
}

struct TyUsePureWalker<'a, 'vir> {
    deps: &'a mut task_encoder::TaskEncoderDependencies<'vir, TyUsePureEnc>,
    args_t: GArgsTy<'vir>,
    args: GArgs<'vir>,
}

impl<'a, 'vir> TyUsePureWalker<'a, 'vir> {
    fn new(deps: &'a mut task_encoder::TaskEncoderDependencies<'vir, TyUsePureEnc>, args: GArgs<'vir>) -> Self {
        let args_t = deps.require_dep::<GArgsTyEnc>(args).unwrap();
        TyUsePureWalker { deps, args_t, args }
    }

    fn encode_ty(&mut self, ty: TyData<'vir, (RustTyDatas, PureTyDatas)>) -> TySpecifics<'vir, UsePureTyDatas> {
        match &ty.specifics {
            TySpecifics::Param(data) => TySpecifics::mk_param(*data.1),
            TySpecifics::Opaque(data) => TySpecifics::mk_opaque(*data.1),
            TySpecifics::Primitive(data) => TySpecifics::mk_primitive(*data.1),
            TySpecifics::ImmRef(data) => {
                let caster = self.encode_normalized(*data.0, ty.0.params);
                TySpecifics::mk_immref(TyUsePureImmRef { caster, pure: *data.1 })
            }
            TySpecifics::MutRef(data) => {
                let caster = self.encode_normalized(*data.0, ty.0.params);
                TySpecifics::mk_mutref(TyUsePureMutRef { caster, pure: *data.1 })
            }
            TySpecifics::StructLike(data) =>
                TySpecifics::StructLike(self.encode_structlike(data, ty.0.params)),
            TySpecifics::EnumLike(data) =>
                TySpecifics::EnumLike(self.encode_enumlike(data, ty.0.params)),
        }
    }

    fn encode_normalized(
        &mut self,
        inner: LazyRustTy<'vir>,
        params: GParams<'vir>,
    ) -> FieldCaster<'vir> {
        let normalized = inner.decompose_compare_normalize(params, self.args);
        self.deps.require_dep::<GArgsCastEnc<Pure>>(normalized).unwrap()
    }

    fn encode_structlike(
        &mut self,
        data: &StructData<'vir, (RustTyDatas, PureTyDatas)>,
        params: GParams<'vir>,
    ) -> StructData<'vir, UsePureTyDatas> {
        let fields = data
            .fields
            .iter()
            .map(|field| {
                let caster = self.encode_normalized(field.0.ty(), params);
                TyUsePureField { caster, pure: *field.1 }
            })
            .collect::<Vec<_>>();
        let data = TyUsePureStructData { args: self.args_t, pure: *data.1 };
        StructData::new(data, fields)
    }

    fn encode_enumlike(
        &mut self,
        data: &EnumData<'vir, (RustTyDatas, PureTyDatas)>,
        params: GParams<'vir>,
    ) -> EnumData<'vir, UsePureTyDatas> {
        let variants = data
            .variants
            .iter()
            .map(|variant| {
                let structlike = self.encode_structlike(&variant.inner, params);
                VariantData::new(*variant.1, structlike)
            })
            .collect::<Vec<_>>();
        EnumData::new(*data.1, variants)
    }
}

impl<'vir> TyUsePureRef<'vir> {
    pub fn unreachable_to_snap<Curr, Next>(&self) -> vir::ExprGenSnap<'vir, Curr, Next> {
        self.ty_pure_ref.unreachable_to_snap.call()(self.args.get_ty())
    }
}

impl<'vir> TyUsePureImmRef<'vir> {
    pub fn prim_to_snap<Curr, Next>(
        &self,
        ref_: vir::ExprGenRef<'vir, Curr, Next>,
        inner: vir::ExprGenSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenCSnap<'vir, Curr, Next> {
        let inner = self.caster.cast_to_callee_ctx(inner);
        self.pure.prim_to_snap.call()(ref_, inner.downcast_ty())
    }

    pub fn value_access<Curr, Next>(
        &self,
        snap: vir::ExprGenCSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        let value = self.pure.value_access.call()(snap);
        self.caster.cast_to_caller_ctx(value.upcast_ty())
    }
}

impl<'vir> TyUsePureMutRef<'vir> {
    pub fn prim_to_snap<Curr, Next>(
        &self,
        ref_: vir::ExprGenRef<'vir, Curr, Next>,
        inner: vir::ExprGenSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenCSnap<'vir, Curr, Next> {
        let inner = self.caster.cast_to_callee_ctx(inner);
        self.pure.prim_to_snap.call()(ref_, inner.downcast_ty())
    }

    pub fn deref_access<Curr, Next>(
        &self,
        snap: vir::ExprGenCSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenRef<'vir, Curr, Next> {
        self.pure.deref_access.call()(snap)
    }

    pub fn value_access<Curr, Next>(
        &self,
        snap: vir::ExprGenCSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
       let value = self.pure.value_access.call()(snap);
        self.caster.cast_to_caller_ctx(value.upcast_ty())
    }
}

impl<'vir> TyUsePureStruct<'vir> {
    pub fn field_snaps_to_snap<Curr, Next>(
        &self,
        mut snaps: Vec<vir::ExprGenSnap<'vir, Curr, Next>>,
    ) -> vir::ExprGenCSnap<'vir, Curr, Next> {
        assert_eq!(snaps.len(), self.fields.len());
        for (snap, field) in snaps.iter_mut().zip(&self.fields) {
            *snap = field.caster.cast_to_callee_ctx(*snap);
        }
        self.pure.field_snaps_to_snap.call()(&snaps)
    }
}

impl<'vir> TyUsePureField<'vir> {
    pub fn read<Curr, Next>(
        &self,
        snap: vir::ExprGenCSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        let res = self.pure.read.call()(snap);
        self.caster.cast_to_caller_ctx(res)
    }
}

impl<'vir> TyUsePureEnum<'vir> {
    pub fn snap_to_discr_snap<Curr, Next>(
        &self,
        snap: vir::ExprGenCSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenCSnap<'vir, Curr, Next> {
        self.snap_to_discr_snap.call()(snap)
    }
}
