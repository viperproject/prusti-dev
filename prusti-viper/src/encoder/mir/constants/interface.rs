use log::debug;
use rustc_middle::{mir, span_bug, ty};
use vir_crate::{
    common::expression::BinaryOperationHelpers,
    high::{self as vir_high, operations::ty::Typed},
};

use crate::encoder::{
    errors::{EncodingError, EncodingResult},
    mir::types::MirTypeEncoderInterface,
};

pub(crate) trait ConstantsEncoderInterface<'tcx> {
    fn encode_constant_high(
        &self,
        constant: &mir::Constant<'tcx>,
    ) -> EncodingResult<vir_high::Expression>;
}

impl<'v, 'tcx: 'v> ConstantsEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn encode_constant_high(
        &self,
        constant: &mir::Constant<'tcx>,
    ) -> EncodingResult<vir_high::Expression> {
        // FIXME: encode_snapshot_constant also handled non literal constants
        let value = match constant.literal {
            mir::ConstantKind::Ty(ty::Const { val, .. }) => *val,
            mir::ConstantKind::Val(val, _) => ty::ConstKind::Value(val),
        };
        let mir_type = constant.ty();
        let scalar_value = self.const_eval_intlike(&value)?;

        let expr = match mir_type.kind() {
            ty::TyKind::Bool => scalar_value.to_bool().unwrap().into(),
            ty::TyKind::Char => scalar_value.to_char().unwrap().into(),
            ty::TyKind::Int(ty::IntTy::I8) => scalar_value.to_i8().unwrap().into(),
            ty::TyKind::Int(ty::IntTy::I16) => scalar_value.to_i16().unwrap().into(),
            ty::TyKind::Int(ty::IntTy::I32) => scalar_value.to_i32().unwrap().into(),
            ty::TyKind::Int(ty::IntTy::I64) => scalar_value.to_i64().unwrap().into(),
            ty::TyKind::Int(ty::IntTy::I128) => scalar_value.to_i128().unwrap().into(),
            ty::TyKind::Int(ty::IntTy::Isize) => {
                let number: isize = scalar_value
                    .to_machine_isize(&self.env().tcx())
                    .unwrap()
                    .try_into()
                    .unwrap();
                number.into()
            }
            ty::TyKind::Uint(ty::UintTy::U8) => scalar_value.to_u8().unwrap().into(),
            ty::TyKind::Uint(ty::UintTy::U16) => scalar_value.to_u16().unwrap().into(),
            ty::TyKind::Uint(ty::UintTy::U32) => scalar_value.to_u32().unwrap().into(),
            ty::TyKind::Uint(ty::UintTy::U64) => scalar_value.to_u64().unwrap().into(),
            ty::TyKind::Uint(ty::UintTy::U128) => scalar_value.to_u128().unwrap().into(),
            ty::TyKind::Uint(ty::UintTy::Usize) => {
                let number: usize = scalar_value
                    .to_machine_usize(&self.env().tcx())
                    .unwrap()
                    .try_into()
                    .unwrap();
                number.into()
            }
            ty::TyKind::FnDef(def_id, _) => {
                self.encode_spec_funcs(*def_id)?;
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
            _ => {
                return Err(EncodingError::unsupported(format!(
                    "unsupported constant type {:?}",
                    mir_type.kind()
                )));
            }
        };
        debug!("encode_const_expr {:?} --> {:?}", value, expr);
        Ok(expr)
    }
}
