//! A public interface to the pure function encoder.

use super::encoder_poly::{FunctionCallInfo, FunctionCallInfoHigh, PureFunctionEncoder};
use crate::encoder::{
    errors::{SpannedEncodingResult, WithSpan},
    mir::specifications::SpecificationsInterface,
    snapshot::interface::SnapshotEncoderInterface,
    stub_function_encoder::StubFunctionEncoder,
    Encoder,
};
use log::{debug, trace};
use prusti_common::config;
use prusti_interface::data::ProcedureDefId;
use prusti_rustc_interface::{
    middle::{mir, ty, ty::GenericArgsRef},
    span::Span,
};
use rustc_hash::{FxHashMap, FxHashSet};

use prusti_interface::specs::typed::ProcedureSpecificationKind;
use std::cell::RefCell;
use vir_crate::{common::identifier::WithIdentifier, high as vir_high, polymorphic as vir_poly};

/// Key of stored call infos, consisting of the `DefId` of the called function,
/// the normalised type substitutions, and the function signature after type
/// substitution and normalisation. The second and third components are stored
/// to account for different monomorphisations resulting from the function
/// being called from callers (with different parameter environments). Each
/// variant of a pure function will be encoded as a separate Viper function.
/// Lifetimes/regions are erased.
type Key<'tcx> = (ProcedureDefId, GenericArgsRef<'tcx>, ty::PolyFnSig<'tcx>);

/// Compute the key for the given call.
fn compute_key<'v, 'tcx: 'v>(
    encoder: &crate::encoder::encoder::Encoder<'v, 'tcx>,
    proc_def_id: ProcedureDefId,
    caller_def_id: ProcedureDefId,
    substs: GenericArgsRef<'tcx>,
) -> SpannedEncodingResult<Key<'tcx>> {
    let tcx = encoder.env().tcx();
    Ok((
        proc_def_id,
        tcx.erase_regions(substs),
        encoder
            .env()
            .query
            .get_fn_sig_resolved(proc_def_id, substs, caller_def_id),
    ))
    /*
    let tcx = encoder.env().tcx();
    let sig = if tcx.is_closure(proc_def_id) {
        substs.as_closure().sig()
    } else {
        tcx.fn_sig(proc_def_id)
    };
    let param_env = tcx.param_env(caller_def_id);
    let sig = tcx.subst_and_normalize_erasing_regions(substs, param_env, sig);
    let substs = tcx.subst_and_normalize_erasing_regions(
        substs,
        param_env,
        encoder.env().identity_substs(proc_def_id),
    );
    Ok((proc_def_id, substs, sig.inputs_and_output().skip_binder()))
    */
}

type FunctionConstructor<'v, 'tcx> = Box<
    dyn FnOnce(
            &crate::encoder::encoder::Encoder<'v, 'tcx>,
        ) -> SpannedEncodingResult<vir_high::FunctionDecl>
        + 'tcx,
>;

/// Depending on the context of the pure encoding,
/// panics will be encoded slightly differently.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) enum PureEncodingContext {
    /// Panics will be encoded as calls to unreachable functions
    /// (which have a `requires false` pre-condition).
    Code,
    /// Indicates that a panic should be encoded to a `false` boolean value.
    /// This flag is used to distinguish whether an assert terminators generated e.g. for an
    /// integer overflow should be translated into `false` and when to an "unreachable" function
    /// call with a `false` precondition.
    Assertion,
    /// Whether the current pure expression that's being encoded sits inside a trigger closure.
    /// Viper limits the type of expressions that are allowed in quantifier triggers and
    /// this requires special care when encoding array/slice accesses which may come with
    /// bound checks included in the MIR. For this purpose, paths that might panic will
    /// be stripped away during the trigger encoding.
    Trigger,
}

#[derive(Default)]
pub(crate) struct PureFunctionEncoderState<'v, 'tcx: 'v> {
    bodies_high: RefCell<FxHashMap<Key<'tcx>, vir_high::Expression>>,
    bodies_poly: RefCell<FxHashMap<Key<'tcx>, vir_poly::Expr>>,
    /// Information necessary to encode a function call. FIXME: Remove this one
    /// and have only call_infos_high.
    call_infos_poly: RefCell<FxHashMap<Key<'tcx>, FunctionCallInfo>>,
    /// Information necessary to encode a function call.
    call_infos_high: RefCell<FxHashMap<Key<'tcx>, FunctionCallInfoHigh>>,
    /// Pure functions whose encoding started (and potentially already
    /// finished). This is used to break recursion.
    pure_functions_encoding_started: RefCell<FxHashSet<Key<'tcx>>>,
    // A mapping from the function identifier to an information needed to encode
    // that function.
    function_descriptions:
        RefCell<FxHashMap<vir_poly::FunctionIdentifier, FunctionDescription<'tcx>>>,
    /// Mapping from keys on MIR level to function identifiers on VIR level.
    function_identifiers: RefCell<FxHashMap<Key<'tcx>, vir_poly::FunctionIdentifier>>,
    /// Encoded functions. The encoding of these functions was triggered by the
    /// definition collector requesting their definition.
    functions: RefCell<FxHashMap<String, std::rc::Rc<vir_high::FunctionDecl>>>,
    /// Callbacks that know how to lazily construct the specified function.
    function_constructors: RefCell<FxHashMap<String, FunctionConstructor<'v, 'tcx>>>,
    /// Stores the procedure id such that it can be used to create a counterexample
    function_proc_ids: RefCell<FxHashMap<String, ProcedureDefId>>,
}

/// The information necessary to encode a function definition.
#[derive(Clone, Debug)]
pub(crate) struct FunctionDescription<'tcx> {
    proc_def_id: ProcedureDefId,
    parent_def_id: ProcedureDefId,
    substs: GenericArgsRef<'tcx>,
}

pub(crate) trait PureFunctionEncoderInterface<'v, 'tcx> {
    fn encode_uneval_const(
        &self,
        c: mir::UnevaluatedConst<'tcx>,
    ) -> SpannedEncodingResult<vir_poly::Expr>;

    fn encode_pure_expression(
        &self,
        proc_def_id: ProcedureDefId,
        parent_def_id: ProcedureDefId,
        substs: GenericArgsRef<'tcx>,
    ) -> SpannedEncodingResult<vir_poly::Expr>;

    /// Encode the body of the given procedure as a pure expression.
    fn encode_pure_expression_high(
        &self,
        proc_def_id: ProcedureDefId,
        parent_def_id: ProcedureDefId,
        substs: GenericArgsRef<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression>;

    /// Encode the pure function definition.
    fn encode_pure_function_def(
        &self,
        proc_def_id: ProcedureDefId,
        parent_def_id: ProcedureDefId,
        substs: GenericArgsRef<'tcx>,
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
        substs: GenericArgsRef<'tcx>,
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
        substs: GenericArgsRef<'tcx>,
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

    fn get_proc_def_id(&self, identifier: String) -> Option<ProcedureDefId>;
}

impl<'v, 'tcx: 'v> PureFunctionEncoderInterface<'v, 'tcx>
    for crate::encoder::encoder::Encoder<'v, 'tcx>
{
    fn get_proc_def_id(&self, identifier: String) -> Option<ProcedureDefId> {
        self.pure_function_encoder_state
            .function_proc_ids
            .borrow()
            .get(&identifier)
            .cloned()
    }

    fn encode_pure_expression_high(
        &self,
        proc_def_id: ProcedureDefId,
        parent_def_id: ProcedureDefId,
        substs: GenericArgsRef<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        let key = compute_key(self, proc_def_id, parent_def_id, substs)?;
        if !self
            .pure_function_encoder_state
            .bodies_high
            .borrow()
            .contains_key(&key)
        {
            let body = super::encoder_high::encode_pure_expression(
                self,
                proc_def_id,
                if self.is_encoding_trigger.get() {
                    // quantifier triggers might not evaluate to boolean
                    PureEncodingContext::Trigger
                } else {
                    PureEncodingContext::Assertion
                },
                parent_def_id,
                substs,
            )?;
            assert!(self
                .pure_function_encoder_state
                .bodies_high
                .borrow_mut()
                .insert(key, body)
                .is_none());
        }
        Ok(self.pure_function_encoder_state.bodies_high.borrow()[&key].clone())
    }

    fn encode_uneval_const(
        &self,
        mir::UnevaluatedConst {
            def,
            args,
            promoted,
        }: mir::UnevaluatedConst<'tcx>,
    ) -> SpannedEncodingResult<vir_poly::Expr> {
        let promoted_id = promoted.expect("unevaluated const should have a promoted ID");
        super::encoder_poly::encode_promoted(self, def, promoted_id, def, args)
    }

    // FIXME: This should be refactored to depend on encode_pure_expression_high
    // and moved to prusti-viper/src/encoder/high/pure_functions/interface.rs
    fn encode_pure_expression(
        &self,
        proc_def_id: ProcedureDefId,
        parent_def_id: ProcedureDefId,
        substs: GenericArgsRef<'tcx>,
    ) -> SpannedEncodingResult<vir_poly::Expr> {
        let key = compute_key(self, proc_def_id, parent_def_id, substs)?;
        if !self
            .pure_function_encoder_state
            .bodies_poly
            .borrow()
            .contains_key(&key)
        {
            let body = super::encoder_poly::encode_body(
                self,
                proc_def_id,
                if self.is_encoding_trigger.get() {
                    // quantifier triggers might not evaluate to boolean
                    PureEncodingContext::Trigger
                } else {
                    PureEncodingContext::Assertion
                },
                parent_def_id,
                substs,
            )?;
            self.pure_function_encoder_state
                .bodies_poly
                .borrow_mut()
                .insert(key, body);
        }
        Ok(self.pure_function_encoder_state.bodies_poly.borrow()[&key].clone())
    }

    #[tracing::instrument(level = "debug", skip(self))]
    fn encode_pure_function_def(
        &self,
        proc_def_id: ProcedureDefId,
        parent_def_id: ProcedureDefId,
        substs: GenericArgsRef<'tcx>,
    ) -> SpannedEncodingResult<()> {
        assert!(
            self.is_pure(proc_def_id, Some(substs)),
            "procedure is not marked as pure: {proc_def_id:?}"
        );

        let mir_span = self.env().query.get_def_span(proc_def_id);
        let key = compute_key(self, proc_def_id, parent_def_id, substs)?;
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
                .insert(key);

            let mut pure_function_encoder = PureFunctionEncoder::new(
                self,
                proc_def_id,
                PureEncodingContext::Code,
                parent_def_id,
                substs,
            );

            let is_bodyless = self.is_trusted(proc_def_id, Some(substs))
                || !self.env().query.has_body(proc_def_id);

            let maybe_identifier: SpannedEncodingResult<vir_poly::FunctionIdentifier> = (|| {
                let proc_kind = self.get_proc_kind(proc_def_id, Some(substs));
                let mut function = if is_bodyless {
                    pure_function_encoder.encode_bodyless_function()?
                } else {
                    match proc_kind {
                        ProcedureSpecificationKind::Predicate(Some(predicate_body)) => {
                            pure_function_encoder.encode_predicate_function(&predicate_body)?
                        }
                        ProcedureSpecificationKind::Predicate(None) => {
                            pure_function_encoder.encode_bodyless_function()?
                        }
                        ProcedureSpecificationKind::Pure => {
                            let function = pure_function_encoder.encode_function()?;
                            if config::use_new_encoder() {
                                // Test the new encoding.
                                let _ = super::encoder_high::encode_function_decl(
                                    self,
                                    proc_def_id,
                                    proc_def_id,
                                    substs,
                                )?;
                            }
                            function
                        }
                        ProcedureSpecificationKind::Impure => {
                            unreachable!("trying to encode an impure function in pure encoder")
                        }
                    }
                };

                let needs_patching = matches!(
                    proc_kind,
                    ProcedureSpecificationKind::Pure
                        | ProcedureSpecificationKind::Predicate(Some(_)),
                );
                if needs_patching {
                    self.mirror_encoder
                        .borrow_mut()
                        .encode_mirrors(proc_def_id, &mut function);
                }

                function = self
                    .patch_snapshots_function(function)
                    .with_span(mir_span)?;

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
                    debug!("Error encoding pure function: {:?}", proc_def_id);
                    let function = if !is_bodyless {
                        let pure_fn_body =
                            self.env()
                                .body
                                .get_pure_fn_body(proc_def_id, substs, parent_def_id);
                        let encoder = StubFunctionEncoder::new(
                            self,
                            proc_def_id,
                            Some(&pure_fn_body),
                            substs,
                            pure_function_encoder.sig,
                        );
                        encoder.encode_function()?
                    } else {
                        let encoder = StubFunctionEncoder::new(
                            self,
                            proc_def_id,
                            None,
                            substs,
                            pure_function_encoder.sig,
                        );
                        encoder.encode_function()?
                    };
                    self.log_vir_program_before_viper(function.to_string());
                    let identifier = self.insert_function(function);
                    self.pure_function_encoder_state
                        .function_identifiers
                        .borrow_mut()
                        .insert(key, identifier);
                }
            }
        }
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
                function_description.parent_def_id,
                function_description.substs,
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
        substs: GenericArgsRef<'tcx>,
    ) -> SpannedEncodingResult<(String, vir_poly::Type)> {
        assert!(
            self.is_pure(proc_def_id, Some(substs)),
            "procedure is not marked as pure: {proc_def_id:?}"
        );

        let key = compute_key(self, proc_def_id, parent_def_id, substs)?;

        let mut call_infos = self
            .pure_function_encoder_state
            .call_infos_poly
            .borrow_mut();
        if let std::collections::hash_map::Entry::Vacant(e) = call_infos.entry(key) {
            // Compute information necessary to encode the function call and
            // memoize it.
            let pure_function_encoder = PureFunctionEncoder::new(
                self,
                proc_def_id,
                PureEncodingContext::Code,
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
                    parent_def_id,
                    substs,
                });

            e.insert(function_call_info);
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
        substs: GenericArgsRef<'tcx>,
    ) -> SpannedEncodingResult<(String, vir_high::Type)> {
        assert!(
            self.is_pure(proc_def_id, Some(substs)),
            "procedure is not marked as pure: {proc_def_id:?}"
        );

        let key = compute_key(self, proc_def_id, parent_def_id, substs)?;

        let mut call_infos = self
            .pure_function_encoder_state
            .call_infos_high
            .borrow_mut();
        if let std::collections::hash_map::Entry::Vacant(e) = call_infos.entry(key) {
            // Compute information necessary to encode the function call and
            // memoize it.
            let function_call_info = super::encoder_high::encode_function_call_info(
                self,
                proc_def_id,
                parent_def_id,
                substs,
            )?;

            let identifier = function_call_info.get_identifier();

            if prusti_common::config::counterexample() {
                self.pure_function_encoder_state
                    .function_proc_ids
                    .borrow_mut()
                    .insert(identifier.clone(), proc_def_id);
            }

            self.register_function_constructor_mir(
                identifier,
                Box::new(move |encoder| {
                    super::encoder_high::encode_function_decl(
                        encoder,
                        proc_def_id,
                        proc_def_id,
                        substs,
                    )
                }),
            )?;

            // FIXME: Refactor encode_pure_function_use to depend on this function.
            if !prusti_common::config::unsafe_core_proof() {
                let _ = self.encode_pure_function_use(proc_def_id, parent_def_id, substs)?;
            }

            e.insert(function_call_info);
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

            let constructor = self
                .pure_function_encoder_state
                .function_constructors
                .borrow_mut()
                .remove(function_identifier);

            // The function is not yet encoded. Trigger the encoding.
            if let Some(constructor) = constructor {
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
