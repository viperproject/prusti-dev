use crate::encoder::{
    errors::{EncodingError, EncodingResult, SpannedEncodingResult},
    mir::pure::PureFunctionEncoderInterface,
};

use vir_crate::{
    high::{self as vir_high, operations::ty::Typed},
    middle::{self as vir_mid, operations::ToMiddleExpression},
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
    fn get_pure_function_decl_high(
        &self,
        function_identifier: &str,
    ) -> SpannedEncodingResult<std::rc::Rc<vir_high::FunctionDecl>>;
    fn get_pure_function_specs_high(
        &self,
        function_identifier: &str,
    ) -> SpannedEncodingResult<(Vec<vir_high::Expression>, Vec<vir_high::Expression>)>;
    /// Returns preconditions and postconditions of the specified pure function.
    fn get_pure_function_specs_mid(
        &self,
        function_identifier: &str,
    ) -> SpannedEncodingResult<(Vec<vir_mid::Expression>, Vec<vir_mid::Expression>)>;
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
            vec![], // FIXME: This is most likely wrong.
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
        let element_type = extract_container_element_type(&container)?;
        let return_type = element_type.clone();
        Ok(vir_high::Expression::function_call(
            name,
            vec![element_type.clone()],
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
        let element_type = extract_container_element_type(&container)?;
        let pure_lifetime = vir_high::ty::Lifetime {
            name: String::from("pure_erased"),
        };
        let return_type =
            vir_high::Type::reference(vir_high::Type::slice(element_type.clone()), pure_lifetime);
        Ok(vir_high::Expression::function_call(
            name,
            vec![element_type.clone()],
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
        let element_type = extract_container_element_type(&container)?;
        let return_type = vir_high::Type::Int(vir_high::ty::Int::Usize);
        Ok(vir_high::Expression::function_call(
            name,
            vec![element_type.clone()],
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
        let element_type = extract_container_element_type(&container)?;
        Ok(vir_high::Expression::function_call(
            name,
            vec![element_type.clone()],
            vec![container],
            target_container_type,
        ))
    }

    fn get_pure_function_decl_high(
        &self,
        function_identifier: &str,
    ) -> SpannedEncodingResult<std::rc::Rc<vir_high::FunctionDecl>> {
        self.get_pure_function_decl_mir(function_identifier)
    }

    fn get_pure_function_specs_high(
        &self,
        function_identifier: &str,
    ) -> SpannedEncodingResult<(Vec<vir_high::Expression>, Vec<vir_high::Expression>)> {
        let function_decl = self.get_pure_function_decl_high(function_identifier)?;
        let pres = function_decl.pres.clone();
        let posts = function_decl.posts.clone();
        Ok((pres, posts))
    }

    fn get_pure_function_specs_mid(
        &self,
        function_identifier: &str,
    ) -> SpannedEncodingResult<(Vec<vir_mid::Expression>, Vec<vir_mid::Expression>)> {
        let (pres, posts) = self.get_pure_function_specs_high(function_identifier)?;
        Ok((
            pres.to_middle_expression(self)?,
            posts.to_middle_expression(self)?,
        ))
    }
}

fn extract_container_element_type(
    container: &vir_high::Expression,
) -> EncodingResult<&vir_high::Type> {
    match container.get_type() {
        vir_high::Type::Array(vir_high::ty::Array { element_type, .. })
        | vir_high::Type::Slice(vir_high::ty::Slice { element_type, .. })
        | vir_high::Type::Reference(vir_high::ty::Reference {
            target_type: box vir_high::Type::Array(vir_high::ty::Array { element_type, .. }),
            ..
        })
        | vir_high::Type::Reference(vir_high::ty::Reference {
            target_type: box vir_high::Type::Slice(vir_high::ty::Slice { element_type, .. }),
            ..
        }) => Ok(&**element_type),
        container_ty => Err(EncodingError::unsupported(format!(
            "unsupported container: {}",
            container_ty
        ))),
    }
}
