use crate::encoder::{
    errors::SpannedEncodingResult,
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        lowerer::{FunctionsLowererInterface, Lowerer},
        predicates::owned::builders::{
            FracRefRangeSnapFunctionBuilder, OwnedAliasedRangeSnapFunctionBuilder,
            UniqueRefCurrentRangeSnapFunctionBuilder, UniqueRefFinalRangeSnapFunctionBuilder,
        },
    },
};

use vir_crate::middle::{self as vir_mid};

impl<'p, 'v: 'p, 'tcx: 'v> Lowerer<'p, 'v, 'tcx> {
    pub(in super::super) fn encode_owned_predicate_range_snapshot(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        super::guard!(self, encoded_owned_predicate_range_snapshot_functions, ty);
        // let ty_identifier = ty.get_identifier();
        // if self
        //     .state()
        //     .encoded_owned_predicate_range_snapshot_functions
        //     .contains(&ty_identifier)
        // {
        //     return Ok(());
        // }
        // self
        //     .state()
        //     .encoded_owned_predicate_range_snapshot_functions
        //     .insert(ty_identifier);

        let type_decl = self.encoder.get_type_decl_mid(ty)?;
        let normalized_type = ty.normalize_type();
        let mut builder =
            OwnedAliasedRangeSnapFunctionBuilder::new(self, &normalized_type, &type_decl)?;
        builder.create_parameters()?;
        builder.add_owned_precondition()?;
        builder.add_postcondition()?;
        let function = builder.build()?;
        self.declare_function(function)?;
        Ok(())
    }

    pub(in super::super) fn encode_unique_ref_predicate_current_range_snapshot(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        super::guard!(
            self,
            encoded_unique_ref_predicate_current_range_snapshot_functions,
            ty
        );
        let type_decl = self.encoder.get_type_decl_mid(ty)?;
        let normalized_type = ty.normalize_type();
        let mut builder =
            UniqueRefCurrentRangeSnapFunctionBuilder::new(self, &normalized_type, &type_decl)?;
        builder.create_parameters()?;
        builder.add_owned_precondition()?;
        builder.add_postcondition()?;
        let function = builder.build()?;
        self.declare_function(function)?;
        Ok(())
    }

    pub(in super::super) fn encode_unique_ref_predicate_final_range_snapshot(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        super::guard!(
            self,
            encoded_unique_ref_predicate_final_range_snapshot_functions,
            ty
        );
        let type_decl = self.encoder.get_type_decl_mid(ty)?;
        let normalized_type = ty.normalize_type();
        let mut builder =
            UniqueRefFinalRangeSnapFunctionBuilder::new(self, &normalized_type, &type_decl)?;
        builder.create_parameters()?;
        // builder.add_owned_precondition()?;
        builder.add_postcondition()?;
        // let function = builder.build()?;
        // self.declare_function(function)?;
        builder.build()?;
        Ok(())
    }

    pub(in super::super) fn encode_frac_ref_predicate_range_snapshot(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        super::guard!(
            self,
            encoded_frac_ref_predicate_range_snapshot_functions,
            ty
        );
        let type_decl = self.encoder.get_type_decl_mid(ty)?;
        let normalized_type = ty.normalize_type();
        let mut builder = FracRefRangeSnapFunctionBuilder::new(self, &normalized_type, &type_decl)?;
        builder.create_parameters()?;
        builder.add_owned_precondition()?;
        builder.add_postcondition()?;
        let function = builder.build()?;
        self.declare_function(function)?;
        Ok(())
    }
}
