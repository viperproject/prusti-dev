use prusti_rustc_interface::middle::ty;
use vir_crate::high::{self as vir_high};

use crate::{encoder::errors::EncodingResult, error_unsupported};

pub(crate) trait CastsEncoderInterface<'tcx> {
    fn encode_int_cast_high(
        &self,
        value: u128,
        ty: ty::Ty<'tcx>,
    ) -> EncodingResult<vir_high::Expression>;
}

impl<'v, 'tcx: 'v> CastsEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    #[tracing::instrument(level = "debug", skip(self), ret)]
    fn encode_int_cast_high(
        &self,
        value: u128,
        ty: ty::Ty<'tcx>,
    ) -> EncodingResult<vir_high::Expression> {
        let expr = match ty.kind() {
            ty::TyKind::Bool => (value != 0).into(),
            ty::TyKind::Int(ty::IntTy::I8) => {
                let number = value as i8;
                number.into()
            }
            ty::TyKind::Int(ty::IntTy::I16) => {
                let number = value as i16;
                number.into()
            }
            ty::TyKind::Int(ty::IntTy::I32) => {
                let number = value as i32;
                number.into()
            }
            ty::TyKind::Int(ty::IntTy::I64) => {
                let number = value as i64;
                number.into()
            }
            ty::TyKind::Int(ty::IntTy::I128) => {
                let number = value as i128;
                number.into()
            }
            ty::TyKind::Int(ty::IntTy::Isize) => {
                let number = value as isize;
                number.into()
            }
            ty::TyKind::Uint(ty::UintTy::U8) => {
                let number = value as u8;
                number.into()
            }
            ty::TyKind::Uint(ty::UintTy::U16) => {
                let number = value as u16;
                number.into()
            }
            ty::TyKind::Uint(ty::UintTy::U32) => {
                let number = value as u32;
                number.into()
            }
            ty::TyKind::Uint(ty::UintTy::U64) => {
                let number = value as u64;
                number.into()
            }
            ty::TyKind::Uint(ty::UintTy::U128) => {
                let number = value;
                number.into()
            }
            ty::TyKind::Uint(ty::UintTy::Usize) => {
                let number = value as usize;
                number.into()
            }
            ty::TyKind::Char => {
                let number = char::from_u32(value.try_into().unwrap()).unwrap();
                number.into()
            }
            kind => {
                error_unsupported!("unsupported integer cast: {:?}", kind);
            }
        };
        Ok(expr)
    }
}
