use crate::encoder::{
    errors::{EncodingError, EncodingResult, SpannedEncodingResult},
    high::to_middle::HighToMiddle,
    mir::pure::PureFunctionEncoderInterface,
};
use vir_crate::{
    high::{self as vir_high, operations::ty::Typed},
    middle::{self as vir_mid},
};

pub(crate) trait HighPureFunctionEncoderInterface<'tcx> {
    // TODO: Replace all these functions with BuiltinFuncApp.
    fn encode_discriminant_call(
        &self,
        adt: vir_high::Expression,
        return_type: vir_high::Type,
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
    fn get_pure_function_decl_mid(
        &mut self,
        function_identifier: &str,
    ) -> SpannedEncodingResult<vir_mid::FunctionDecl>;
    /// Returns preconditions and postconditions of the specified pure function.
    fn get_pure_function_specs_mid(
        &mut self,
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
        return_type: vir_high::Type,
    ) -> EncodingResult<vir_high::Expression> {
        Ok(vir_high::Expression::builtin_func_app_no_pos(
            vir_high::BuiltinFunc::Discriminant,
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
        // TODO: Consider if instead of a builtin function, we should have a
        // dedicated variant on the expression.
        let element_type = extract_container_element_type(&container)?;
        let return_type = element_type.clone();
        Ok(vir_high::Expression::builtin_func_app_no_pos(
            vir_high::BuiltinFunc::Index,
            vec![element_type.clone()],
            vec![container, index],
            return_type,
        ))
    }

    /// Encode subslicing of an array/slice.
    // FIXME: Check if encode_subslice_call is used and tested
    fn encode_subslice_call(
        &self,
        container: vir_high::Expression,
        _range: vir_high::Expression,
    ) -> EncodingResult<vir_high::Expression> {
        // FIXME: Should use encode_builtin_function_use.
        let _name = "subslice";
        let _element_type = extract_container_element_type(&container)?;
        // let pure_lifetime = vir_high::ty::LifetimeConst::erased();
        let _pure_lifetime = unimplemented!();
        // let return_type = vir_high::Type::reference(
        //     pure_lifetime,
        //     vir_high::ty::Uniqueness::Shared,
        //     // FIXME: add slice lifetimes for subslice_call
        //     vir_high::Type::slice(element_type.clone(), vec![]),
        // );
        // Ok(vir_high::Expression::function_call(
        //     name,
        //     vec![element_type.clone()],
        //     vec![container, range],
        //     return_type,
        // ))
    }

    /// Encode len of a slice.
    fn encode_len_call(
        &self,
        container: vir_high::Expression,
    ) -> EncodingResult<vir_high::Expression> {
        let element_type = extract_container_element_type(&container)?;
        let return_type = vir_high::Type::Int(vir_high::ty::Int::Usize);
        Ok(vir_high::Expression::builtin_func_app_no_pos(
            vir_high::BuiltinFunc::Len,
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

    fn get_pure_function_decl_mid(
        &mut self,
        function_identifier: &str,
    ) -> SpannedEncodingResult<vir_mid::FunctionDecl> {
        let function_decl = self.get_pure_function_decl_high(function_identifier)?;
        Ok(vir_mid::FunctionDecl {
            name: function_decl.name.clone(),
            type_arguments: function_decl.type_arguments.clone().high_to_middle(self)?,
            parameters: function_decl.parameters.clone().high_to_middle(self)?,
            return_type: function_decl.return_type.clone().high_to_middle(self)?,
            pres: function_decl.pres.clone().high_to_middle(self)?,
            posts: function_decl.posts.clone().high_to_middle(self)?,
            body: function_decl
                .body
                .clone()
                .map(|body| body.high_to_middle(self))
                .transpose()?,
        })
    }

    fn get_pure_function_specs_mid(
        &mut self,
        function_identifier: &str,
    ) -> SpannedEncodingResult<(Vec<vir_mid::Expression>, Vec<vir_mid::Expression>)> {
        let (pres, posts) = self.get_pure_function_specs_high(function_identifier)?;
        Ok((pres.high_to_middle(self)?, posts.high_to_middle(self)?))
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
            "unsupported container: {container_ty}"
        ))),
    }
}
