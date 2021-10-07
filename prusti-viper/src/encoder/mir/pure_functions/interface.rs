//! A public interface to the pure function encoder.

use std::{
    cell::{Ref, RefCell},
    collections::{HashMap, HashSet},
};

use super::encoder::{FunctionCallInfo, PureFunctionEncoder};
use crate::encoder::{
    encoder::SubstMap,
    errors::{SpannedEncodingResult, WithSpan},
    stub_function_encoder::StubFunctionEncoder,
};
use log::{debug, trace};
use prusti_interface::{data::ProcedureDefId, environment::Environment};
use rustc_middle::ty::TyCtxt;
use vir_crate::polymorphic as vir;

type Key = (ProcedureDefId, String);

#[derive(Default)]
pub(crate) struct PureFunctionEncoderState<'tcx> {
    bodies: RefCell<HashMap<Key, vir::Expr>>,
    /// Information necessar to encode a function call.
    call_infos: RefCell<HashMap<Key, FunctionCallInfo>>,
    /// Pure functions whose encoding started (and potentially already
    /// finished). This is used to break recursion.
    pure_functions_encoding_started: RefCell<HashSet<(ProcedureDefId, String)>>,
    // A mapping from the function identifier to an information needed to encode
    // that function.
    function_descriptions: RefCell<HashMap<vir::FunctionIdentifier, FunctionDescription<'tcx>>>,
    /// Mapping from keys on MIR level to function identifiers on VIR level.
    function_identifiers: RefCell<HashMap<Key, vir::FunctionIdentifier>>,
}

/// The information necessary to encode a function definition.
#[derive(Clone, Debug)]
pub(crate) struct FunctionDescription<'tcx> {
    proc_def_id: ProcedureDefId,
    substs: SubstMap<'tcx>,
}

pub(crate) trait PureFunctionEncoderInterface<'tcx> {
    /// Encode the body of the given procedure as a pure expression.
    fn encode_pure_expression(
        &self,
        proc_def_id: ProcedureDefId,
        parent_def_id: ProcedureDefId,
        substs: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<vir::Expr>;

    /// Encode the pure function definition.
    fn encode_pure_function_def(
        &self,
        proc_def_id: ProcedureDefId,
        tymap: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<()>;

    /// Ensure that the function with the specified identifier is encoded.
    fn ensure_pure_function_encoded(
        &self,
        identifier: &vir::FunctionIdentifier,
    ) -> SpannedEncodingResult<()>;

    /// Encode the use (call) of a pure function, returning the name of the
    /// function and its type.
    ///
    /// The called function must be marked as pure. It should be local unless
    /// there is an external specification defined.
    fn encode_pure_function_use(
        &self,
        proc_def_id: ProcedureDefId,
        parent_def_id: ProcedureDefId,
        substs: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<(String, vir::Type)>;
}

impl<'v, 'tcx: 'v> PureFunctionEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn encode_pure_expression(
        &self,
        proc_def_id: ProcedureDefId,
        parent_def_id: ProcedureDefId,
        substs: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<vir::Expr> {
        let mir_span = self.env().tcx().def_span(proc_def_id);
        let substs_key = self.type_substitution_key(substs).with_span(mir_span)?;
        let key = (proc_def_id, substs_key);
        if !self
            .pure_function_encoder_state
            .bodies
            .borrow()
            .contains_key(&key)
        {
            let procedure = self.env().get_procedure(proc_def_id);
            let pure_function_encoder = PureFunctionEncoder::new(
                self,
                proc_def_id,
                procedure.get_mir(),
                true,
                parent_def_id,
                substs,
            );
            let body = pure_function_encoder.encode_body()?;
            self.pure_function_encoder_state
                .bodies
                .borrow_mut()
                .insert(key.clone(), body);
        }
        Ok(self.pure_function_encoder_state.bodies.borrow()[&key].clone())
    }

    fn encode_pure_function_def(
        &self,
        proc_def_id: ProcedureDefId,
        tymap: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<()> {
        trace!("[enter] encode_pure_function_def({:?})", proc_def_id);
        assert!(
            self.is_pure(proc_def_id),
            "procedure is not marked as pure: {:?}",
            proc_def_id
        );

        // FIXME: Using substitutions as a key is most likely wrong.
        let mir_span = self.env().tcx().def_span(proc_def_id);
        let substs_key = self.type_substitution_key(tymap).with_span(mir_span)?;
        let key = (proc_def_id, substs_key);

        if !self
            .pure_function_encoder_state
            .function_identifiers
            .borrow()
            .contains_key(&key)
            && !self
                .pure_function_encoder_state
                .pure_functions_encoding_started
                .borrow()
                .contains(&key)
        {
            trace!("not encoded: {:?}", key);

            self.pure_function_encoder_state
                .pure_functions_encoding_started
                .borrow_mut()
                .insert(key.clone());

            let wrapper_def_id = self.get_wrapper_def_id(proc_def_id);
            let procedure = self.env().get_procedure(wrapper_def_id);
            let pure_function_encoder = PureFunctionEncoder::new(
                self,
                proc_def_id,
                procedure.get_mir(),
                false,
                proc_def_id,
                tymap,
            );

            let maybe_identifier: SpannedEncodingResult<vir::FunctionIdentifier> = (|| {
                let (mut function, needs_patching) =
                    if let Some(predicate_body) = self.get_predicate_body(proc_def_id) {
                        (
                            pure_function_encoder.encode_predicate_function(predicate_body)?,
                            false,
                        )
                    } else if self.is_trusted(proc_def_id) {
                        (pure_function_encoder.encode_bodyless_function()?, false)
                    } else {
                        (pure_function_encoder.encode_function()?, true)
                    };

                if needs_patching {
                    self.mirror_encoder
                        .borrow_mut()
                        .encode_mirrors(proc_def_id, &mut function);
                }

                function = self
                    .snapshot_encoder
                    .borrow_mut()
                    .patch_snapshots_function(self, function, tymap)
                    .with_span(procedure.get_span())?;

                self.log_vir_program_before_viper(function.to_string());
                Ok(self.insert_function(function))
            })();
            match maybe_identifier {
                Ok(identifier) => {
                    self.pure_function_encoder_state
                        .function_identifiers
                        .borrow_mut()
                        .insert(key, identifier);
                }
                Err(error) => {
                    self.register_encoding_error(error);
                    debug!(
                        "Error encoding pure function: {:?} wrapper_def_id={:?}",
                        proc_def_id, wrapper_def_id
                    );
                    let body = self.env().external_mir(wrapper_def_id);
                    let stub_encoder = StubFunctionEncoder::new(self, proc_def_id, body, tymap);
                    let function = stub_encoder.encode_function()?;
                    self.log_vir_program_before_viper(function.to_string());
                    let identifier = self.insert_function(function);
                    self.pure_function_encoder_state
                        .function_identifiers
                        .borrow_mut()
                        .insert(key, identifier);
                }
            }
        }

        trace!("[exit] encode_pure_function_def({:?})", proc_def_id);
        Ok(())
    }

    fn ensure_pure_function_encoded(
        &self,
        identifier: &vir::FunctionIdentifier,
    ) -> SpannedEncodingResult<()> {
        let function_descriptions = self
            .pure_function_encoder_state
            .function_descriptions
            .borrow();
        if let Some(function_description) = function_descriptions.get(identifier) {
            let function_description = function_description.clone();
            // We need to release the borrow here before encoding the function
            // because otherwise encoding recursive functions cause a panic.
            drop(function_descriptions);
            self.encode_pure_function_def(
                function_description.proc_def_id,
                &function_description.substs,
            )?;
        } else {
            // FIXME: We probably should not fail silently here…
        }
        Ok(())
    }

    fn encode_pure_function_use(
        &self,
        proc_def_id: ProcedureDefId,
        parent_def_id: ProcedureDefId,
        substs: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<(String, vir::Type)> {
        assert!(
            self.is_pure(proc_def_id),
            "procedure is not marked as pure: {:?}",
            proc_def_id
        );

        let mir_span = self.env().tcx().def_span(proc_def_id);
        let substs_key = self.type_substitution_key(substs).with_span(mir_span)?;
        let key = (proc_def_id, substs_key);

        let mut call_infos = self.pure_function_encoder_state.call_infos.borrow_mut();
        if !call_infos.contains_key(&key) {
            // Compute information necessary to encode the function call and
            // memoize it.
            let wrapper_def_id = self.get_wrapper_def_id(proc_def_id);
            let procedure = self.env().get_procedure(wrapper_def_id);
            let pure_function_encoder = PureFunctionEncoder::new(
                self,
                proc_def_id,
                procedure.get_mir(),
                false,
                parent_def_id,
                substs,
            );
            let function_call_info = pure_function_encoder.encode_function_call_info()?;

            // Save the information necessary to encode the function definition.
            let function_identifier: vir::FunctionIdentifier =
                vir::WithIdentifier::get_identifier(&function_call_info).into();
            let mut function_descriptions = self
                .pure_function_encoder_state
                .function_descriptions
                .borrow_mut();
            let description = FunctionDescription {
                proc_def_id,
                substs: substs.clone(),
            };
            assert!(function_descriptions
                .insert(function_identifier, description)
                .is_none());

            call_infos.insert(key.clone(), function_call_info);
        }
        let function_call_info = &call_infos[&key];

        Ok((
            function_call_info.name.clone(),
            function_call_info.return_type.clone(),
        ))
    }
}
