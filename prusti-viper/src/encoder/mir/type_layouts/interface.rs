use crate::encoder::{
    errors::SpannedEncodingResult,
    mir::{pure::PureFunctionEncoderInterface, types::MirTypeEncoderInterface},
};
use rustc_hash::FxHashSet;
use rustc_middle::ty;
use std::cell::RefCell;
use vir_crate::{common::identifier::WithIdentifier, high as vir_high};

#[derive(Default)]
pub(crate) struct MirTypeLayoutsEncoderState {
    registered_size_functions: RefCell<FxHashSet<vir_high::Type>>,
}

pub(crate) trait MirTypeLayoutsEncoderInterface<'tcx> {
    fn encode_type_size_expression(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression>;
}

impl<'v, 'tcx: 'v> MirTypeLayoutsEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn encode_type_size_expression(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        let mut encoded_ty = self.encode_type_high(ty)?;
        encoded_ty.erase_lifetime();
        let function_call = vir_high::expression::FuncApp::new(
            "size",
            vec![encoded_ty.clone()],
            Vec::new(),
            Vec::new(),
            vir_high::ty::Type::Int(vir_high::ty::Int::Usize),
        );
        if !self
            .mir_type_layouts_encoder_state
            .registered_size_functions
            .borrow()
            .contains(&encoded_ty)
        {
            let encoded_ty_clone = encoded_ty.clone();
            self.register_function_constructor_mir(
                function_call.get_identifier(),
                Box::new(move |_encoder| {
                    Ok(vir_high::FunctionDecl::new(
                        "size",
                        vec![encoded_ty_clone],
                        Vec::new(),
                        vir_high::ty::Type::Int(vir_high::ty::Int::Usize),
                        Vec::new(),
                        Vec::new(),
                        None,
                    ))
                }),
            )?;
            self.mir_type_layouts_encoder_state
                .registered_size_functions
                .borrow_mut()
                .insert(encoded_ty);
        }
        Ok(vir_high::Expression::FuncApp(function_call))
    }
}
