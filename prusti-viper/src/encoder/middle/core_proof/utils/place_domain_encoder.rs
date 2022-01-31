use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::lowerer::{DomainsLowererInterface, Lowerer},
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
    fn encode_expression(
        &mut self,
        place: &vir_mid::Expression,
        lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        assert!(place.is_place(), "{} is not a place", place);
        let result = match place {
            vir_mid::Expression::Local(local) => self.encode_local(local, lowerer)?,
            vir_mid::Expression::Field(field) => {
                let arg = self.encode_expression(&*field.base, lowerer)?;
                let domain_name = self.domain_name(lowerer);
                lowerer.encode_field_access_function_app(
                    domain_name,
                    arg,
                    field.base.get_type(),
                    &field.field,
                    field.position,
                )?
            }
            x => unimplemented!("{}", x),
        };
        Ok(result)
    }
}
