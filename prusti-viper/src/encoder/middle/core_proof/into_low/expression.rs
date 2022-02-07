use crate::encoder::{
    errors::{SpannedEncodingError, SpannedEncodingResult},
    middle::core_proof::{lowerer::FunctionsLowererInterface, snapshots::IntoSnapshot},
};
use vir_crate::{
    common::identifier::WithIdentifier, low as vir_low, low::operations::ToLowLowerer,
    middle as vir_mid,
};

impl<'p, 'v: 'p, 'tcx: 'v> ToLowLowerer for super::super::lowerer::Lowerer<'p, 'v, 'tcx> {
    type Error = SpannedEncodingError;

    fn to_low_expression_downcast(
        &mut self,
        _variant: vir_mid::expression::Downcast,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        todo!()
    }

    fn to_low_func_app(
        &mut self,
        app: vir_mid::expression::FuncApp,
    ) -> SpannedEncodingResult<vir_low::expression::FuncApp> {
        let function_name = app.get_identifier();
        let arguments = self.to_low_vec_expression(app.arguments)?;
        let return_type = self.to_low_type(app.return_type)?;
        let position = self.to_low_position(app.position)?;
        let func_app = self.create_func_app(function_name, arguments, return_type, position)?;
        Ok(func_app)
    }

    fn to_low_position(
        &mut self,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Position> {
        Ok(position)
    }

    fn to_low_variable_decl(
        &mut self,
        decl: vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        Ok(vir_low::VariableDecl {
            name: decl.name,
            ty: self.to_low_type(decl.ty)?,
        })
    }

    fn to_low_type(&mut self, ty: vir_mid::Type) -> SpannedEncodingResult<vir_low::Type> {
        ty.create_snapshot(self)
    }

    fn to_low_labelled_old(
        &mut self,
        expression: vir_mid::expression::LabelledOld,
    ) -> Result<vir_low::expression::LabelledOld, Self::Error> {
        Ok(vir_low::expression::LabelledOld {
            label: Some(expression.label),
            base: Box::new(self.to_low_expression(*expression.base)?),
            position: self.to_low_position(expression.position)?,
        })
    }

    fn to_low_constant_value_fn_ptr(
        &mut self,
    ) -> Result<vir_low::expression::ConstantValue, Self::Error> {
        todo!()
    }

    fn to_low_float_const(
        &mut self,
        _expression: vir_mid::expression::FloatConst,
    ) -> Result<vir_low::expression::FloatConst, Self::Error> {
        todo!()
    }

    fn to_low_expression_addr_of(
        &mut self,
        _expression: vir_mid::expression::AddrOf,
    ) -> Result<vir_low::Expression, Self::Error> {
        todo!()
    }

    fn to_low_expression_deref(
        &mut self,
        _expression: vir_mid::expression::Deref,
    ) -> Result<vir_low::Expression, Self::Error> {
        todo!()
    }

    fn to_low_field_decl(
        &mut self,
        _field: vir_mid::FieldDecl,
    ) -> Result<vir_low::FieldDecl, Self::Error> {
        todo!()
    }

    fn to_low_expression_variant(
        &mut self,
        _expression: vir_mid::expression::Variant,
    ) -> Result<vir_low::Expression, Self::Error> {
        todo!()
    }

    fn to_low_expression_constructor(
        &mut self,
        _expression: vir_mid::expression::Constructor,
    ) -> Result<vir_low::Expression, Self::Error> {
        todo!()
    }
}
