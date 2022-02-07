//! A public interface to the pure function encoder.

use super::encoder::{FunctionCallInfo, FunctionCallInfoHigh, PureFunctionEncoder};
use crate::encoder::{
    encoder::SubstMap,
    errors::{SpannedEncodingResult, WithSpan},
    mir::generics::MirGenericsEncoderInterface,
    snapshot::interface::SnapshotEncoderInterface,
    stub_function_encoder::StubFunctionEncoder,
};
use log::{debug, trace};
use prusti_interface::data::ProcedureDefId;
use rustc_hash::{FxHashMap, FxHashSet};

use std::cell::RefCell;
use vir_crate::{common::identifier::WithIdentifier, high as vir_high, polymorphic as vir_poly};

type Key = (ProcedureDefId, Vec<vir_high::Type>);
type FunctionConstructor<'v, 'tcx> = Box<
    dyn FnOnce(
        &crate::encoder::encoder::Encoder<'v, 'tcx>,
    ) -> SpannedEncodingResult<vir_high::FunctionDecl>,
>;

#[derive(Default)]
pub(crate) struct PureFunctionEncoderState<'v, 'tcx: 'v> {
    bodies_high: RefCell<FxHashMap<Key, vir_high::Expression>>,
    bodies_poly: RefCell<FxHashMap<Key, vir_poly::Expr>>,
    /// Information necessary to encode a function call. FIXME: Remove this one
    /// and have only call_infos_high.
    call_infos_poly: RefCell<FxHashMap<Key, FunctionCallInfo>>,
    /// Information necessary to encode a function call.
    call_infos_high: RefCell<FxHashMap<Key, FunctionCallInfoHigh>>,
    /// Pure functions whose encoding started (and potentially already
    /// finished). This is used to break recursion.
    pure_functions_encoding_started: RefCell<FxHashSet<Key>>,
    // A mapping from the function identifier to an information needed to encode
    // that function.
    function_descriptions:
        RefCell<FxHashMap<vir_poly::FunctionIdentifier, FunctionDescription<'tcx>>>,
    /// Mapping from keys on MIR level to function identifiers on VIR level.
    function_identifiers: RefCell<FxHashMap<Key, vir_poly::FunctionIdentifier>>,
    /// Encoded functions. The encoding of these functions was triggered by the
    /// definition collector requesting their definition.
    functions: RefCell<FxHashMap<String, std::rc::Rc<vir_high::FunctionDecl>>>,
    /// Callbacks that know how to lazily construct the specified function.
    function_constructors: RefCell<FxHashMap<String, FunctionConstructor<'v, 'tcx>>>,
}

/// The information necessary to encode a function definition.
#[derive(Clone, Debug)]
pub(crate) struct FunctionDescription<'tcx> {
    proc_def_id: ProcedureDefId,
    substs: SubstMap<'tcx>,
}

pub(crate) trait PureFunctionEncoderInterface<'v, 'tcx> {
    fn encode_pure_expression(
        &self,
        proc_def_id: ProcedureDefId,
        parent_def_id: ProcedureDefId,
        substs: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<vir_poly::Expr>;

    /// Encode the body of the given procedure as a pure expression.
    fn encode_pure_expression_high(
        &self,
        proc_def_id: ProcedureDefId,
        parent_def_id: ProcedureDefId,
        substs: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression>;

    /// Encode the pure function definition.
    fn encode_pure_function_def(
        &self,
        proc_def_id: ProcedureDefId,
        substs: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<()>;

    /// Ensure that the function with the specified identifier is encoded.
    fn ensure_pure_function_encoded(
        &self,
        identifier: &vir_poly::FunctionIdentifier,
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
    ) -> SpannedEncodingResult<(String, vir_poly::Type)>;

    /// Encode the use (call) of a pure function, returning the name of the
    /// function and its type.
    ///
    /// The called function must be marked as pure. It should be local unless
    /// there is an external specification defined.
    fn encode_pure_function_use_high(
        &self,
        proc_def_id: ProcedureDefId,
        parent_def_id: ProcedureDefId,
        substs: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<(String, vir_high::Type)>;

    /// Get the encoded function declaration.
    ///
    /// This will trigger the encoding of the function declaration if needed.
    fn get_pure_function_decl_mir(
        &self,
        function_identifier: &str,
    ) -> SpannedEncodingResult<std::rc::Rc<vir_high::FunctionDecl>>;

    fn register_function_constructor_mir(
        &self,
        function_identifier: String,
        constructor: FunctionConstructor<'v, 'tcx>,
    ) -> SpannedEncodingResult<()>;
}

impl<'v, 'tcx: 'v> PureFunctionEncoderInterface<'v, 'tcx>
    for crate::encoder::encoder::Encoder<'v, 'tcx>
{
    fn encode_pure_expression_high(
        &self,
        proc_def_id: ProcedureDefId,
        parent_def_id: ProcedureDefId,
        substs: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        let mir_span = self.env().tcx().def_span(proc_def_id);
        let substs_key = self
            .encode_generic_arguments_high(proc_def_id, substs)
            .with_span(mir_span)?;
        let key = (proc_def_id, substs_key);
        if !self
            .pure_function_encoder_state
            .bodies_high
            .borrow()
            .contains_key(&key)
        {
            let procedure = self.env().get_procedure(proc_def_id);
            let body = super::new_encoder::encode_pure_expression(
                self,
                proc_def_id,
                procedure.get_mir(),
                parent_def_id,
                substs,
            )?;
            assert!(self
                .pure_function_encoder_state
                .bodies_high
                .borrow_mut()
                .insert(key.clone(), body)
                .is_none());
        }
        Ok(self.pure_function_encoder_state.bodies_high.borrow()[&key].clone())
    }

    // FIXME: This should be refactored to depend on encode_pure_expression_high
    // and moved to prusti-viper/src/encoder/high/pure_functions/interface.rs
    fn encode_pure_expression(
        &self,
        proc_def_id: ProcedureDefId,
        parent_def_id: ProcedureDefId,
        substs: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<vir_poly::Expr> {
        let mir_span = self.env().tcx().def_span(proc_def_id);
        let substs_key = self
            .encode_generic_arguments_high(proc_def_id, substs)
            .with_span(mir_span)?;
        let key = (proc_def_id, substs_key);
        if !self
            .pure_function_encoder_state
            .bodies_poly
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
                .bodies_poly
                .borrow_mut()
                .insert(key.clone(), body);
        }
        Ok(self.pure_function_encoder_state.bodies_poly.borrow()[&key].clone())
    }

    fn encode_pure_function_def(
        &self,
        proc_def_id: ProcedureDefId,
        substs: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<()> {
        trace!("[enter] encode_pure_function_def({:?})", proc_def_id);
        assert!(
            self.is_pure(proc_def_id),
            "procedure is not marked as pure: {:?}",
            proc_def_id
        );

        // FIXME: Using substitutions as a key is most likely wrong.
        let mir_span = self.env().tcx().def_span(proc_def_id);
        let substs_key = self
            .encode_generic_arguments_high(proc_def_id, substs)
            .with_span(mir_span)?;
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
                substs,
            );

            let maybe_identifier: SpannedEncodingResult<vir_poly::FunctionIdentifier> = (|| {
                let (mut function, needs_patching) =
                    if let Some(predicate_body) = self.get_predicate_body(proc_def_id) {
                        (
                            pure_function_encoder.encode_predicate_function(predicate_body)?,
                            false,
                        )
                    } else if self.is_trusted(proc_def_id) {
                        (pure_function_encoder.encode_bodyless_function()?, false)
                    } else {
                        let function = pure_function_encoder.encode_function()?;
                        // Test the new encoding.
                        let _ = super::new_encoder::encode_function_decl(
                            self,
                            proc_def_id,
                            procedure.get_mir(),
                            proc_def_id,
                            substs,
                        )?;
                        (function, true)
                    };

                if needs_patching {
                    self.mirror_encoder
                        .borrow_mut()
                        .encode_mirrors(proc_def_id, &mut function);
                }

                function = self
                    .patch_snapshots_function(function, substs)
                    .with_span(procedure.get_span())?;

                self.log_vir_program_before_viper(function.to_string());
                Ok(self.insert_function(function))
            })(
            );
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
                    let stub_encoder = StubFunctionEncoder::new(self, proc_def_id, body, substs);
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
        identifier: &vir_poly::FunctionIdentifier,
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
    ) -> SpannedEncodingResult<(String, vir_poly::Type)> {
        assert!(
            self.is_pure(proc_def_id),
            "procedure is not marked as pure: {:?}",
            proc_def_id
        );

        let mir_span = self.env().tcx().def_span(proc_def_id);
        let substs_key = self
            .encode_generic_arguments_high(proc_def_id, substs)
            .with_span(mir_span)?;
        let key = (proc_def_id, substs_key);

        let mut call_infos = self
            .pure_function_encoder_state
            .call_infos_poly
            .borrow_mut();
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
            let function_identifier: vir_poly::FunctionIdentifier =
                WithIdentifier::get_identifier(&function_call_info).into();
            let mut function_descriptions = self
                .pure_function_encoder_state
                .function_descriptions
                .borrow_mut();
            // Then `function_identifier` may be the same with a different `key`.
            // This is because the substitution map `substs` context may differ,
            // but the pure function call does not use these generics.
            // For instance a pure function call in a trait and then a trait impl;
            // in the former `substs` is empty, but in the latter the generic `Self` is mapped.
            function_descriptions
                .entry(function_identifier)
                .or_insert(FunctionDescription {
                    proc_def_id,
                    substs: substs.clone(),
                });

            call_infos.insert(key.clone(), function_call_info);
        }
        let function_call_info = &call_infos[&key];

        Ok((
            function_call_info.name.clone(),
            function_call_info.return_type.clone(),
        ))
    }

    fn encode_pure_function_use_high(
        &self,
        proc_def_id: ProcedureDefId,
        parent_def_id: ProcedureDefId,
        substs: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<(String, vir_high::Type)> {
        assert!(
            self.is_pure(proc_def_id),
            "procedure is not marked as pure: {:?}",
            proc_def_id
        );

        let mir_span = self.env().tcx().def_span(proc_def_id);
        let substs_key = self
            .encode_generic_arguments_high(proc_def_id, substs)
            .with_span(mir_span)?;
        let key = (proc_def_id, substs_key);

        let mut call_infos = self
            .pure_function_encoder_state
            .call_infos_high
            .borrow_mut();
        if !call_infos.contains_key(&key) {
            // Compute information necessary to encode the function call and
            // memoize it.
            let wrapper_def_id = self.get_wrapper_def_id(proc_def_id);
            let procedure = self.env().get_procedure(wrapper_def_id);
            let function_call_info = super::new_encoder::encode_function_call_info(
                self,
                proc_def_id,
                procedure.get_mir(),
                parent_def_id,
                substs,
            )?;

            // FIXME: Refactor encode_pure_function_use to depend on this function.
            let _ = self.encode_pure_function_use(proc_def_id, parent_def_id, substs)?;

            call_infos.insert(key.clone(), function_call_info);
        }
        let function_call_info = &call_infos[&key];

        Ok((
            function_call_info.name.clone(),
            function_call_info.return_type.clone(),
        ))
    }

    fn get_pure_function_decl_mir(
        &self,
        function_identifier: &str,
    ) -> SpannedEncodingResult<std::rc::Rc<vir_high::FunctionDecl>> {
        let functions_borrow = self.pure_function_encoder_state.functions.borrow();
        if let Some(function) = functions_borrow.get(function_identifier) {
            // The function is already encoded.
            Ok(function.clone())
        } else {
            drop(functions_borrow); // Release the borrow.

            // The function is not yet encoded. Trigger the encoding.
            if let Some(constructor) = self
                .pure_function_encoder_state
                .function_constructors
                .borrow_mut()
                .remove(function_identifier)
            {
                let function = std::rc::Rc::new(constructor(self)?);
                let identifier = function.get_identifier();
                assert_eq!(&identifier, function_identifier);
                self.pure_function_encoder_state
                    .functions
                    .borrow_mut()
                    .insert(identifier, function.clone());
                Ok(function)
            } else {
                unreachable!("not found constructor for {}", function_identifier);
            }
        }
    }

    fn register_function_constructor_mir(
        &self,
        function_identifier: String,
        constructor: FunctionConstructor<'v, 'tcx>,
    ) -> SpannedEncodingResult<()> {
        assert!(self
            .pure_function_encoder_state
            .function_constructors
            .borrow_mut()
            .insert(function_identifier, constructor)
            .is_none());
        Ok(())
    }
}
