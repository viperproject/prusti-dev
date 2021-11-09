use super::super::lower::IntoPolymorphic;
use crate::encoder::{
    encoder::SubstMap,
    errors::{EncodingError, EncodingResult, SpannedEncodingResult, WithSpan},
    mir::pure::PureFunctionEncoderInterface,
    snapshot::interface::SnapshotEncoderInterface,
    stub_function_encoder::StubFunctionEncoder,
};
use log::{debug, trace};
use prusti_interface::{data::ProcedureDefId, environment::Environment};
use rustc_middle::ty::TyCtxt;
use std::{
    cell::{Ref, RefCell},
    collections::{HashMap, HashSet},
};
use vir_crate::{
    high::{self as vir_high, operations::ty::Typed},
    polymorphic as vir_poly,
};

pub(crate) trait HighPureFunctionEncoderInterface<'tcx> {
    fn encode_discriminant_call(
        &self,
        adt: vir_high::Expression,
    ) -> EncodingResult<vir_high::Expression>;
    fn encode_index_call(
        &self,
        container: vir_high::Expression,
        index: vir_high::Expression,
    ) -> EncodingResult<vir_high::Expression>;
    fn encode_subslice_call(
        &self,
        container: vir_high::Expression,
        range: vir_high::Expression,
    ) -> EncodingResult<vir_high::Expression>;
    fn encode_len_call(
        &self,
        container: vir_high::Expression,
    ) -> EncodingResult<vir_high::Expression>;
    fn encode_cast_into_slice(
        &self,
        container: vir_high::Expression,
        target_container_type: vir_high::Type,
    ) -> EncodingResult<vir_high::Expression>;
}

impl<'v, 'tcx: 'v> HighPureFunctionEncoderInterface<'tcx>
    for crate::encoder::encoder::Encoder<'v, 'tcx>
{
    /// Encode enum discriminant lookup.
    fn encode_discriminant_call(
        &self,
        adt: vir_high::Expression,
    ) -> EncodingResult<vir_high::Expression> {
        let name = "discriminant";
        let return_type = vir_high::Type::Int(vir_high::ty::Int::Isize);
        Ok(vir_high::Expression::function_call(
            name,
            vec![adt],
            return_type,
        ))
    }

    /// Encode index into a slice or array.
    fn encode_index_call(
        &self,
        container: vir_high::Expression,
        index: vir_high::Expression,
    ) -> EncodingResult<vir_high::Expression> {
        // FIXME: Should use encode_builtin_function_use.
        let name = "lookup_pure";
        let return_type = {
            match container.get_type() {
                vir_high::Type::Array(vir_high::ty::Array { element_type, .. })
                | vir_high::Type::Slice(vir_high::ty::Slice { element_type }) => {
                    (**element_type).clone()
                }
                container_ty => {
                    return Err(EncodingError::unsupported(format!(
                        "calling index on unsupported container: {}",
                        container_ty
                    )))
                }
            }
        };
        Ok(vir_high::Expression::function_call(
            name,
            vec![container, index],
            return_type,
        ))
    }

    /// Encode subslicing of an array/slice.
    fn encode_subslice_call(
        &self,
        container: vir_high::Expression,
        range: vir_high::Expression,
    ) -> EncodingResult<vir_high::Expression> {
        // FIXME: Should use encode_builtin_function_use.
        let name = "subslice";
        let return_type = {
            match container.get_type() {
                vir_high::Type::Reference(vir_high::ty::Reference {
                    target_type: box vir_high::Type::Array(vir_high::ty::Array { element_type, .. }),
                })
                | vir_high::Type::Reference(vir_high::ty::Reference {
                    target_type: box vir_high::Type::Slice(vir_high::ty::Slice { element_type, .. }),
                }) => vir_high::Type::reference(vir_high::Type::slice((**element_type).clone())),
                container_ty => {
                    return Err(EncodingError::unsupported(format!(
                        "calling index on unsupported container: {}",
                        container_ty
                    )))
                }
            }
        };
        Ok(vir_high::Expression::function_call(
            name,
            vec![container, range],
            return_type,
        ))
    }

    /// Encode len of a slice.
    fn encode_len_call(
        &self,
        container: vir_high::Expression,
    ) -> EncodingResult<vir_high::Expression> {
        // FIXME: Should use encode_builtin_function_use.
        let name = "len";
        let return_type = vir_high::Type::Int(vir_high::ty::Int::Usize);
        Ok(vir_high::Expression::function_call(
            name,
            vec![container],
            return_type,
        ))
    }

    fn encode_cast_into_slice(
        &self,
        container: vir_high::Expression,
        target_container_type: vir_high::Type,
    ) -> EncodingResult<vir_high::Expression> {
        let name = "into_slice";
        // FIXME: Check that argumet types of container and
        // target_container_type match.
        Ok(vir_high::Expression::function_call(
            name,
            vec![container],
            target_container_type,
        ))
    }
}
