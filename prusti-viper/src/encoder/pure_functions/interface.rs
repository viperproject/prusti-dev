//! A public interface to the pure function encoder.

use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
};

use super::encoder::PureFunctionEncoder;
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
pub(crate) struct PureFunctionEncoderState {
    pure_function_bodies: RefCell<HashMap<Key, vir::Expr>>,
    pure_functions: RefCell<HashMap<(ProcedureDefId, String), vir::FunctionIdentifier>>,
    /// Pure functions whose encoding started (and potentially already
    /// finished). This is used to break recursion.
    pure_functions_encoding_started: RefCell<HashSet<(ProcedureDefId, String)>>,
    // TODO: Add a map from vir_legacy::vir::FunctionIdentifier to all
    // information needed to encode the function definition.
}

pub(crate) trait PureFunctionEncoderInterface<'tcx> {
    /// Encode the body of the given procedure as a pure expression.
    fn encode_pure_expression(
        &self,
        proc_def_id: ProcedureDefId,
        parent_def_id: ProcedureDefId,
        substs: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<vir::Expr>;

    fn encode_pure_function_def(
        &self,
        proc_def_id: ProcedureDefId,
        tymap: &SubstMap<'tcx>,
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

impl<'v, 'tcx: 'v> PureFunctionEncoderInterface<'tcx> for super::super::Encoder<'v, 'tcx> {
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
            .pure_function_bodies
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
                .pure_function_bodies
                .borrow_mut()
                .insert(key.clone(), body);
        }
        Ok(self
            .pure_function_encoder_state
            .pure_function_bodies
            .borrow()[&key]
            .clone())
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
        let substs_key = self.type_substitution_key(&tymap).with_span(mir_span)?;
        let key = (proc_def_id, substs_key);

        if !self
            .pure_function_encoder_state
            .pure_functions
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
                &tymap,
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
                    .patch_snapshots_function(self, function, &tymap)
                    .with_span(procedure.get_span())?;

                self.log_vir_program_before_viper(function.to_string());
                Ok(self.insert_function(function))
            })();
            match maybe_identifier {
                Ok(identifier) => {
                    self.pure_function_encoder_state
                        .pure_functions
                        .borrow_mut()
                        .insert(key, identifier);
                }
                Err(error) => {
                    self.register_encoding_error(error.clone());
                    debug!(
                        "Error encoding pure function: {:?} wrapper_def_id={:?}",
                        proc_def_id, wrapper_def_id
                    );
                    let body = self.env().external_mir(wrapper_def_id);
                    let stub_encoder = StubFunctionEncoder::new(self, proc_def_id, body, &tymap);
                    let function = stub_encoder.encode_function()?;
                    self.log_vir_program_before_viper(function.to_string());
                    let identifier = self.insert_function(function);
                    self.pure_function_encoder_state
                        .pure_functions
                        .borrow_mut()
                        .insert(key, identifier);
                }
            }
        }

        trace!("[exit] encode_pure_function_def({:?})", proc_def_id);
        Ok(())
    }

    fn encode_pure_function_use(
        &self,
        proc_def_id: ProcedureDefId,
        parent_def_id: ProcedureDefId,
        substs: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<(String, vir::Type)> {
        let wrapper_def_id = self.get_wrapper_def_id(proc_def_id);
        let procedure = self.env().get_procedure(wrapper_def_id);

        assert!(
            self.is_pure(proc_def_id),
            "procedure is not marked as pure: {:?}",
            proc_def_id
        );

        self.encode_pure_function_def(proc_def_id, substs)?;

        let pure_function_encoder = PureFunctionEncoder::new(
            self,
            proc_def_id,
            procedure.get_mir(),
            false,
            parent_def_id,
            &substs,
        );

        Ok((
            pure_function_encoder.encode_function_name(),
            pure_function_encoder.encode_function_return_type()?,
        ))
    }
}
