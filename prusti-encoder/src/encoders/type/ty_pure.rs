use std::ops::Deref;

use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullResult, TaskEncoder};
use vir::{with_vcx, CastType, FunctionIdn};

use prusti_rustc_interface::{
    abi,
};

use crate::encoders::{domain::{DomainDataEnum, DomainDataField, DomainDataImmRef, DomainDataMutRef, DomainDataPrim, DomainDataStruct, DomainEnc, DomainEncOutput, DomainEncOutputRef, DomainEncSpecifics}, lifted::{casters::{CastFunctionsOutputRef, CastTypePure}, rust_ty_cast::{GenericCasterPure, RustTyCastersEnc}}};

use super::{
    most_generic_ty::extract_type_params,
};

#[derive(Debug, Clone, Copy)]
pub struct TyPureDataImmRef<'vir> {
    param: GenericCasterPure<'vir>,
    data: DomainDataImmRef<'vir>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyPureDataMutRef<'vir> {
    param: GenericCasterPure<'vir>,
    data: DomainDataMutRef<'vir>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyPureDataStruct<'a, 'vir> {
    params: &'a [GenericCasterPure<'vir>],
    data: DomainDataStruct<'vir>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyPureDataField<'vir> {
    param: Option<GenericCasterPure<'vir>>,
    field: DomainDataField<'vir>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyPureDataEnum<'vir> {
    data: DomainDataEnum<'vir>,
}

/// Encodes a type into the snapshot representation. Takes an arbitrary Rust
/// `Ty` and provides a wrapper around the results of the `DomainEnc` encoder.
/// This wrapper handles all the generic casts required.
pub struct TyPureEnc;

#[derive(Clone, Debug)]
pub struct TyPureEncOutputRef<'vir> {
    pub snapshot: vir::TypeSnap<'vir>,
    domain: DomainEncOutputRef<'vir>,
}

#[derive(Clone, Debug)]
pub struct TyPureEncOutput<'vir> {
    inner: TyPureEncOutputRef<'vir>,
    output: DomainEncOutput<'vir>,
    params: Vec<GenericCasterPure<'vir>>,
}

impl<'vir> Deref for TyPureEncOutput<'vir> {
    type Target = TyPureEncOutputRef<'vir>;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<'vir> task_encoder::OutputRefAny for TyPureEncOutputRef<'vir> {}

impl TaskEncoder for TyPureEnc {
    task_encoder::encoder_cache!(TyPureEnc);

    type TaskDescription<'vir> = ty::Ty<'vir>;

    type OutputRef<'vir> = TyPureEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = TyPureEncOutput<'vir>;

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        with_vcx(|vcx| {
            let (generic_ty, args) = extract_type_params(vcx.tcx(), *task_key);
            let domain = deps.require_ref::<DomainEnc>(generic_ty)?;
            let snapshot = (domain.domain)();
            let inner = TyPureEncOutputRef { snapshot, domain };
            deps.emit_output_ref(*task_key, inner.clone())?;
            let mut params = Vec::new();
            for arg in args {
                params.push(deps.require_local::<RustTyCastersEnc<CastTypePure>>(arg)?);
            }
            // TODO: mutable references are unsound since they both hold the
            // inner value in the `p_Ref_mut` predicate as well as the separate
            // indirect predicate.
            if let ty::TyKind::Ref(_, inner_ty, ty::Mutability::Mut) = task_key.kind() {
                params.push(deps.require_local::<RustTyCastersEnc<CastTypePure>>(*inner_ty)?);
            }
            let output = deps.require_dep::<DomainEnc>(generic_ty)?;
            Ok((TyPureEncOutput { inner, output, params }, ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        DomainEnc::emit_outputs(program)
    }
}

impl<'vir> TyPureEncOutputRef<'vir> {
    pub fn unreachable_to_snap(&self) -> FunctionIdn<'vir, (), vir::Snap> {
        self.domain.unreachable_to_snap
    }
}

impl<'vir> TyPureEncOutput<'vir> {
    #[track_caller]
    pub fn expect_primitive(&self) -> DomainDataPrim<'vir> {
        self.output.specifics.expect_primitive()
    }

    pub fn expect_immref(&self) -> TyPureDataImmRef<'vir> {
        assert_eq!(self.params.len(), 1);
        TyPureDataImmRef { param: self.params[0], data: self.output.specifics.expect_immref() }
    }

    pub fn expect_mutref(&self) -> TyPureDataMutRef<'vir> {
        assert_eq!(self.params.len(), 1);
        TyPureDataMutRef { param: self.params[0], data: self.output.specifics.expect_mutref() }
    }

    pub fn expect_structlike(&self) -> TyPureDataStruct<'_, 'vir> {
        TyPureDataStruct { data: self.output.specifics.expect_structlike(), params: &self.params }
    }

    pub fn get_enumlike(&self) -> Option<TyPureDataEnum<'vir>> {
        self.output.specifics.expect_enumlike().map(|data| TyPureDataEnum { data })
    }

    pub fn get_variant_any(&self, variant: abi::VariantIdx) -> TyPureDataStruct<'_, 'vir> {
        TyPureDataStruct { data: self.output.specifics.get_variant_any(variant), params: &self.params }
    }

    pub fn get_variant_opt(&self, variant: Option<abi::VariantIdx>) -> TyPureDataStruct<'_, 'vir> {
        TyPureDataStruct { data: self.output.specifics.get_variant_any(variant.unwrap_or(abi::FIRST_VARIANT)), params: &self.params }
    }
}

impl<'vir> TyPureDataImmRef<'vir> {
    pub fn prim_to_snap<Curr, Next>(
        &self,
        ref_: vir::ExprGenRef<'vir, Curr, Next>,
        inner: vir::ExprGenSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenCSnap<'vir, Curr, Next> {
        let inner = self.param.cast_to_generic_if_necessary(vir::with_vcx(|vcx| vcx), inner);
        self.data.prim_to_snap.call()(ref_, inner)
    }

    pub fn value_access<Curr, Next>(
        &self,
        snap: vir::ExprGenCSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        let value = self.data.value_access.call()(snap);
        self.param.cast_to_concrete_if_possible(vir::with_vcx(|vcx| vcx), value.upcast_ty())
    }
}

impl<'vir> TyPureDataMutRef<'vir> {
    pub fn prim_to_snap<Curr, Next>(
        &self,
        ref_: vir::ExprGenRef<'vir, Curr, Next>,
        inner: vir::ExprGenSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenCSnap<'vir, Curr, Next> {
        let inner = self.param.cast_to_generic_if_necessary(vir::with_vcx(|vcx| vcx), inner);
        self.data.prim_to_snap.call()(ref_, inner)
    }

    pub fn deref_access<Curr, Next>(
        &self,
        snap: vir::ExprGenCSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenRef<'vir, Curr, Next> {
        self.data.deref_access.call()(snap)
    }

    pub fn value_access<Curr, Next>(
        &self,
        snap: vir::ExprGenCSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
       let value = self.data.value_access.call()(snap);
        self.param.cast_to_concrete_if_possible(vir::with_vcx(|vcx| vcx), value.upcast_ty())
    }
}

impl<'a, 'vir> TyPureDataStruct<'a, 'vir> {
    pub fn field_snaps_to_snap<Curr, Next>(
        &self,
        mut snaps: Vec<vir::ExprGenSnap<'vir, Curr, Next>>,
    ) -> vir::ExprGenCSnap<'vir, Curr, Next> {
        assert_eq!(snaps.len(), self.data.field_access.len());
        for (snap, fa) in snaps.iter_mut().zip(self.data.field_access) {
            let Some(gidx) = fa.generic_idx else {
                continue;
            };
            let param = &self.params[gidx as usize];
            *snap = vir::with_vcx(|vcx| param.cast_to_generic_if_necessary(vcx, *snap).upcast_ty());
        }
        self.data.field_snaps_to_snap.call()(&snaps)
    }

    pub fn field(&self, idx: abi::FieldIdx) -> TyPureDataField<'vir> {
        let field = self.data.field_access[idx.as_usize()];
        TyPureDataField {
            param: field.generic_idx.map(|idx| self.params[idx as usize]),
            field,
        }
    }

    pub fn fields(&self) -> impl Iterator<Item = TyPureDataField<'vir>> + '_ {
        (0..self.data.field_access.len()).map(move |idx| self.field(abi::FieldIdx::from_usize(idx)))
    }
}

impl<'vir> TyPureDataField<'vir> {
    pub fn read<Curr, Next>(
        &self,
        snap: vir::ExprGenCSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        let res = self.field.read.call()(snap);
        let Some(param) = self.param else {
            return res;
        };
        param.cast_to_concrete_if_possible(vir::with_vcx(|vcx| vcx), res)
    }
}

impl<'vir> TyPureDataEnum<'vir> {
    pub fn snap_to_discr_snap<Curr, Next>(
        &self,
        snap: vir::ExprGenCSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenCSnap<'vir, Curr, Next> {
        self.data.snap_to_discr_snap.call()(snap)
    }
}
