use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        lowerer::{DomainsLowererInterface, Lowerer},
        snapshots::{IntoSnapshot, SnapshotDomainsInterface, SnapshotValidityInterface},
    },
};
use vir_crate::{
    common::expression::QuantifierHelpers,
    low::{self as vir_low},
    middle::{self as vir_mid},
};

trait Private {
    fn encode_sequence_repeat_constructor_def(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()>;
}

impl<'p, 'v: 'p, 'tcx: 'v> Private for Lowerer<'p, 'v, 'tcx> {
    fn encode_sequence_repeat_constructor_def(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        if !self
            .snapshots_state
            .encoded_sequence_repeat_constructor
            .contains(ty)
        {
            self.snapshots_state
                .encoded_sequence_repeat_constructor
                .insert(ty.clone());

            let element_type = match ty {
                vir_mid::Type::Sequence(vir_mid::ty::Sequence { element_type, .. })
                | vir_mid::Type::Array(vir_mid::ty::Array { element_type, .. }) => element_type,
                _ => {
                    unreachable!("ty: {}", ty);
                }
            };

            let domain_name = self.encode_snapshot_domain_name(ty)?;
            let element_domain_name = self.encode_snapshot_domain_name(element_type)?;
            use vir_low::macros::*;
            var_decls! {
                parameter: {element_type.to_snapshot(self)?},
                count: Int,
                index: Int
            };
            let valid_parameter =
                self.encode_snapshot_valid_call(&element_domain_name, parameter.clone().into())?;
            let sequence = self.encode_sequence_repeat_constructor_call(
                ty,
                parameter.clone().into(),
                count.clone().into(),
            )?;
            let valid_sequence = self.encode_snapshot_valid_call(&domain_name, sequence.clone())?;
            let element = vir_low::Expression::container_op_no_pos(
                vir_low::expression::ContainerOpKind::SeqIndex,
                sequence.clone(),
                index.clone().into(),
            );
            let len = vir_low::Expression::container_op_no_pos(
                vir_low::expression::ContainerOpKind::SeqLen,
                sequence.clone(),
                true.into(),
            );
            let elements = vir_low::Expression::forall(
                vec![index.clone()],
                vec![vir_low::Trigger::new(vec![element.clone()])],
                expr! {
                    (([0.into()] <= index) && (index < count)) ==> ([element] == parameter)
                },
            );
            let body = vir_low::Expression::forall(
                vec![parameter, count.clone()],
                vec![vir_low::Trigger::new(vec![
                    valid_parameter.clone(),
                    sequence,
                ])],
                expr! {
                    ([valid_parameter] && ([0.into()] <= count)) ==> (
                        [valid_sequence] &&
                        (count == [len]) &&
                        [elements]
                    )
                },
            );
            let axiom = vir_low::DomainAxiomDecl {
                name: format!("{}$sequence_repeat_constructor_definition", domain_name),
                body,
            };
            self.declare_axiom(&domain_name, axiom)?;
        }
        Ok(())
    }
}

pub(in super::super::super) trait BuiltinFunctionsInterface {
    fn encode_sequence_repeat_constructor_call(
        &mut self,
        ty: &vir_mid::Type,
        argument: vir_low::Expression,
        count: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>;
}

impl<'p, 'v: 'p, 'tcx: 'v> BuiltinFunctionsInterface for Lowerer<'p, 'v, 'tcx> {
    fn encode_sequence_repeat_constructor_call(
        &mut self,
        ty: &vir_mid::Type,
        argument: vir_low::Expression,
        count: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.encode_sequence_repeat_constructor_def(ty)?;
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        let function_name = format!("sequence_repeat_constructor${}", domain_name);
        let result_type = ty.to_snapshot(self)?;
        self.create_domain_func_app(
            domain_name,
            function_name,
            vec![argument, count],
            result_type,
            Default::default(),
        )
    }
}
