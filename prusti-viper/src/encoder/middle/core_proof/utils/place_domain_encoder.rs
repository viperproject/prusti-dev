use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        lowerer::{DomainsLowererInterface, Lowerer},
        snapshots::IntoProcedureSnapshot,
    },
};
use vir_crate::{
    low as vir_low,
    middle::{self as vir_mid, operations::ty::Typed},
};

pub(in super::super) trait PlaceExpressionDomainEncoder {
    fn domain_name(&mut self, lowerer: &mut Lowerer) -> &str;
    fn encode_local(
        &mut self,
        local: &vir_mid::expression::Local,
        lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_deref(
        &mut self,
        deref: &vir_mid::expression::Deref,
        lowerer: &mut Lowerer,
        arg: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_labelled_old(
        &mut self,
        expression: &vir_mid::expression::LabelledOld,
        lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_array_index_axioms(
        &mut self,
        base_type: &vir_mid::Type,
        lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<()>;
    fn encode_expression(
        &mut self,
        place: &vir_mid::Expression,
        lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        // FIXME: Use ADT domains instead.
        assert!(place.is_place(), "{place} is not a place");
        let result = match place {
            vir_mid::Expression::Local(local) => self.encode_local(local, lowerer)?,
            vir_mid::Expression::Field(field) => {
                let arg = self.encode_expression(&field.base, lowerer)?;
                let domain_name = self.domain_name(lowerer);
                lowerer.encode_field_access_function_app(
                    domain_name,
                    arg,
                    field.base.get_type(),
                    &field.field,
                    field.position,
                )?
            }
            vir_mid::Expression::Variant(variant) => {
                let arg = self.encode_expression(&variant.base, lowerer)?;
                let domain_name = self.domain_name(lowerer);
                lowerer.encode_variant_access_function_app(
                    domain_name,
                    arg,
                    variant.base.get_type(),
                    &variant.variant_index,
                    variant.position,
                )?
            }
            vir_mid::Expression::Deref(deref) => {
                let arg = self.encode_expression(&deref.base, lowerer)?;
                self.encode_deref(deref, lowerer, arg)?
            }
            vir_mid::Expression::BuiltinFuncApp(vir_mid::BuiltinFuncApp {
                function: vir_mid::BuiltinFunc::Index,
                arguments,
                position,
                ..
            }) => {
                assert_eq!(arguments.len(), 2);
                self.encode_array_index_axioms(arguments[0].get_type(), lowerer)?;
                let array = self.encode_expression(&arguments[0], lowerer)?;
                let index = arguments[1].to_procedure_snapshot(lowerer)?;
                let domain_name = self.domain_name(lowerer);
                lowerer.encode_index_access_function_app(
                    domain_name,
                    array,
                    arguments[0].get_type(),
                    index,
                    *position,
                )?
            }
            vir_mid::Expression::LabelledOld(expression) => {
                self.encode_labelled_old(expression, lowerer)?
            }
            vir_mid::Expression::EvalIn(expression) => {
                self.encode_expression(&expression.body, lowerer)?
            }
            x => unimplemented!("{}", x),
        };
        Ok(result)
    }
}
