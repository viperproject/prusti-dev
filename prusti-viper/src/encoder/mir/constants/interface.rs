use prusti_rustc_interface::middle::{mir, ty};
use vir_crate::high::{self as vir_high};

use crate::{
    encoder::{errors::EncodingResult, mir::types::MirTypeEncoderInterface},
    error_unsupported,
};

pub(crate) trait ConstantsEncoderInterface<'tcx> {
    fn encode_constant_high(
        &self,
        constant: &mir::Constant<'tcx>,
    ) -> EncodingResult<vir_high::Expression>;

    fn compute_array_len(&self, size: ty::Const<'tcx>) -> EncodingResult<u64>;
}

impl<'v, 'tcx: 'v> ConstantsEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    #[tracing::instrument(level = "debug", skip(self), ret)]
    fn encode_constant_high(
        &self,
        constant: &mir::Constant<'tcx>,
    ) -> EncodingResult<vir_high::Expression> {
        let mir_type = constant.ty();
        let _ = self.encode_type_high(mir_type)?; // Trigger encoding of the type.
                                                  // FIXME: encode_snapshot_constant also handled non literal constants
        let scalar_value = || self.const_eval_intlike(constant.literal);

        let expr = match mir_type.kind() {
            ty::TyKind::Bool => scalar_value()?.to_bool().unwrap().into(),
            ty::TyKind::Char => scalar_value()?.to_char().unwrap().into(),
            ty::TyKind::Int(ty::IntTy::I8) => scalar_value()?.to_i8().unwrap().into(),
            ty::TyKind::Int(ty::IntTy::I16) => scalar_value()?.to_i16().unwrap().into(),
            ty::TyKind::Int(ty::IntTy::I32) => scalar_value()?.to_i32().unwrap().into(),
            ty::TyKind::Int(ty::IntTy::I64) => scalar_value()?.to_i64().unwrap().into(),
            ty::TyKind::Int(ty::IntTy::I128) => scalar_value()?.to_i128().unwrap().into(),
            ty::TyKind::Int(ty::IntTy::Isize) => {
                let number: isize = scalar_value()?
                    .to_target_isize(&self.env().tcx())
                    .unwrap()
                    .try_into()
                    .unwrap();
                number.into()
            }
            ty::TyKind::Uint(ty::UintTy::U8) => scalar_value()?.to_u8().unwrap().into(),
            ty::TyKind::Uint(ty::UintTy::U16) => scalar_value()?.to_u16().unwrap().into(),
            ty::TyKind::Uint(ty::UintTy::U32) => scalar_value()?.to_u32().unwrap().into(),
            ty::TyKind::Uint(ty::UintTy::U64) => scalar_value()?.to_u64().unwrap().into(),
            ty::TyKind::Uint(ty::UintTy::U128) => scalar_value()?.to_u128().unwrap().into(),
            ty::TyKind::Uint(ty::UintTy::Usize) => {
                let number: usize = scalar_value()?
                    .to_target_usize(&self.env().tcx())
                    .unwrap()
                    .try_into()
                    .unwrap();
                number.into()
            }
            ty::TyKind::FnDef(..) => {
                let ty = self.encode_type_high(mir_type)?;
                vir_high::Expression::constant_no_pos(
                    vir_high::expression::ConstantValue::FnPtr,
                    ty,
                )
            }
            ty::TyKind::Tuple(elements) if elements.is_empty() => {
                let ty = self.encode_type_high(mir_type)?;
                vir_high::Expression::constructor_no_pos(ty, Vec::new())
            }
            ty::TyKind::Ref(_, ty, _) => match ty.kind() {
                ty::TyKind::Str => match constant.literal {
                    mir::ConstantKind::Val(
                        mir::interpret::ConstValue::Slice { data, start, end },
                        _,
                    ) => {
                        let bytes = data
                            .inner()
                            .inspect_with_uninit_and_ptr_outside_interpreter(start..end);
                        let string = std::str::from_utf8(bytes).unwrap().to_string();
                        let ty = self.encode_type_high(mir_type)?;
                        vir_high::Expression::constant_no_pos(
                            vir_high::expression::ConstantValue::String(string),
                            ty,
                        )
                    }
                    _ => {
                        error_unsupported!(
                            "unsupported constant type (3) {:?} {:?} {:?}",
                            mir_type.kind(),
                            ty.kind(),
                            constant.literal
                        );
                    }
                },
                _ => {
                    error_unsupported!(
                        "unsupported constant type (2) {:?} {:?}",
                        mir_type.kind(),
                        ty.kind()
                    );
                }
            },
            _ => {
                error_unsupported!("unsupported constant type (1) {:?}", mir_type.kind());
            }
        };
        Ok(expr)
    }

    fn compute_array_len(&self, size: ty::Const<'tcx>) -> EncodingResult<u64> {
        self.const_eval_intlike(mir::ConstantKind::Ty(size))
            .map(|s| s.to_u64().unwrap())
    }
}
