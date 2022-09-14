use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        lowerer::{DomainsLowererInterface, Lowerer},
        snapshots::{IntoSnapshot, SnapshotValidityInterface, SnapshotValuesInterface},
    },
};
use vir_crate::{
    common::{expression::QuantifierHelpers, identifier::WithIdentifier},
    low as vir_low, middle as vir_mid,
};

const DOMAIN_NAME: &str = "Casts";

pub(in super::super) trait CastsInterface {
    fn cast_int_to_int(
        &mut self,
        source_type: &vir_mid::Type,
        destination_type: &vir_mid::Type,
        arg: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
}

impl<'p, 'v: 'p, 'tcx: 'v> CastsInterface for Lowerer<'p, 'v, 'tcx> {
    fn cast_int_to_int(
        &mut self,
        source_type: &vir_mid::Type,
        destination_type: &vir_mid::Type,
        argument: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let identifier = (
            source_type.get_identifier(),
            destination_type.get_identifier(),
        );
        let function_name = format!("cast${}${}", identifier.0, identifier.1);
        let return_type = destination_type.to_snapshot(self)?;
        if !self.casts_state.encoded_casts.contains(&identifier) {
            self.casts_state.encoded_casts.insert(identifier);
            use vir_low::macros::*;
            var_decls!(parameter: {source_type.to_snapshot(self)?});
            let call = self.create_domain_func_app(
                DOMAIN_NAME,
                function_name.clone(),
                vec![parameter.clone().into()],
                return_type.clone(),
                Default::default(),
            )?;
            let parameter_int = self.obtain_constant_value(
                source_type,
                parameter.clone().into(),
                Default::default(),
            )?;
            let parameter_dst = self.construct_constant_snapshot(
                destination_type,
                parameter_int,
                Default::default(),
            )?;
            let validity =
                self.encode_snapshot_valid_call_for_type(parameter_dst.clone(), destination_type)?;
            let body = vir_low::Expression::forall(
                vec![parameter],
                vec![vir_low::Trigger::new(vec![call.clone()])],
                expr! {
                    [validity] ==> ([call] == [parameter_dst])
                },
            );
            let axiom =
                vir_low::DomainAxiomDecl::new(None, format!("{function_name}$definition"), body);
            self.declare_axiom(DOMAIN_NAME, axiom)?;
        }
        self.create_domain_func_app(
            DOMAIN_NAME,
            function_name,
            vec![argument],
            return_type,
            position,
        )
    }
}
