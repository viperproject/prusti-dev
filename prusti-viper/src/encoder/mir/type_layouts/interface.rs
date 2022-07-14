use crate::encoder::{
    errors::SpannedEncodingResult,
    mir::{
        constants::ConstantsEncoderInterface, pure::PureFunctionEncoderInterface,
        types::MirTypeEncoderInterface,
    },
};
use prusti_rustc_interface::middle::ty;
use rustc_hash::FxHashSet;
use std::cell::RefCell;
use vir_crate::{common::identifier::WithIdentifier, high as vir_high};

#[derive(Default)]
pub(crate) struct MirTypeLayoutsEncoderState {
    registered_size_functions: RefCell<FxHashSet<vir_high::Type>>,
}

pub(crate) trait MirTypeLayoutsEncoderInterface<'tcx> {
    /// Returns the size of memory block containing `count` consequative
    /// elements of `ty` elements. Note that there is no guarantee for `size(c,
    /// ty) == c * size(c, ty)` because of padding.
    fn encode_type_size_expression_with_reps(
        &self,
        count: vir_high::Expression,
        ty: ty::Ty<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression>;
    fn encode_type_size_expression(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression>;
}

impl<'v, 'tcx: 'v> MirTypeLayoutsEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn encode_type_size_expression_with_reps(
        &self,
        count: vir_high::Expression,
        ty: ty::Ty<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        let encoded_ty = self.encode_type_high(ty)?;
        let encoded_ty_without_lifetime = encoded_ty.erase_lifetimes();
        let usize = vir_high::Type::Int(vir_high::ty::Int::Usize);
        let function_call = vir_high::expression::FuncApp::new(
            "size",
            vec![encoded_ty.clone()],
            vec![count],
            vec![vir_high::VariableDecl::new("count", usize.clone())],
            usize,
        );
        if !self
            .mir_type_layouts_encoder_state
            .registered_size_functions
            .borrow()
            .contains(&encoded_ty_without_lifetime)
        {
            let usize = vir_high::Type::Int(vir_high::ty::Int::Usize);
            self.register_function_constructor_mir(
                function_call.get_identifier(),
                Box::new(move |_encoder| {
                    Ok(vir_high::FunctionDecl::new(
                        "size",
                        vec![encoded_ty],
                        vec![vir_high::VariableDecl::new("count", usize.clone())],
                        usize,
                        Vec::new(),
                        Vec::new(),
                        None,
                    ))
                }),
            )?;
            self.mir_type_layouts_encoder_state
                .registered_size_functions
                .borrow_mut()
                .insert(encoded_ty_without_lifetime);
        }
        Ok(vir_high::Expression::FuncApp(function_call))
    }

    fn encode_type_size_expression(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        match ty.kind() {
            ty::TyKind::Array(elem_ty, size) => {
                let array_len: usize = self.compute_array_len(*size).try_into().unwrap();
                self.encode_type_size_expression_with_reps(array_len.into(), *elem_ty)
            }
            _ => self.encode_type_size_expression_with_reps(1usize.into(), ty),
        }
    }
}
