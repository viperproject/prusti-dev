use crate::encoder::{errors::SpannedEncodingResult, mir::types::MirTypeEncoderInterface};
use prusti_rustc_interface::middle::ty;
use vir_crate::high::{self as vir_high, operations::const_generics::WithConstArguments};

pub(crate) trait MirTypeLayoutsEncoderInterface<'tcx> {
    fn encode_type_size_expression_high(
        &self,
        ty: vir_high::Type,
    ) -> SpannedEncodingResult<vir_high::Expression>;
    fn encode_type_size_expression(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression>;
    fn encode_type_padding_size_expression(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression>;
}

impl<'v, 'tcx: 'v> MirTypeLayoutsEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn encode_type_size_expression_high(
        &self,
        ty: vir_high::Type,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        let encoded_ty = ty.erase_lifetimes();
        let usize = vir_high::Type::Int(vir_high::ty::Int::Usize);
        let const_arguments = encoded_ty.get_const_arguments();
        let function_call = vir_high::Expression::builtin_func_app_no_pos(
            vir_high::BuiltinFunc::Size,
            vec![encoded_ty],
            const_arguments,
            usize,
        );
        Ok(function_call)
    }

    fn encode_type_size_expression(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        let encoded_ty = self.encode_type_high(ty)?;
        self.encode_type_size_expression_high(encoded_ty)
        // .erase_lifetimes();
        // let usize = vir_high::Type::Int(vir_high::ty::Int::Usize);
        // let const_arguments = encoded_ty.get_const_arguments();
        // let function_call = vir_high::Expression::builtin_func_app_no_pos(
        //     vir_high::BuiltinFunc::Size,
        //     vec![encoded_ty],
        //     const_arguments,
        //     usize,
        // );
        // Ok(function_call)
    }

    fn encode_type_padding_size_expression(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        let encoded_ty = self.encode_type_high(ty)?;
        let usize = vir_high::Type::Int(vir_high::ty::Int::Usize);
        let function_call = vir_high::Expression::builtin_func_app_no_pos(
            vir_high::BuiltinFunc::PaddingSize,
            vec![encoded_ty],
            Vec::new(),
            usize,
        );
        Ok(function_call)
    }
}
