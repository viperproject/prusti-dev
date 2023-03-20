// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::PositionManager;
use backend_common::VerificationError;
use core::fmt::Debug;
use log::debug;
use prusti_interface::{data::ProcedureDefId, PrustiError};
use prusti_rustc_interface::{errors::MultiSpan, span::source_map::SourceMap};
use rustc_hash::FxHashMap;
use vir_crate::polymorphic::Position;

const ASSERTION_TIMEOUT_HELP_MESSAGE: &str =
    "This could be caused by too small assertion timeout. \
Try increasing it by setting the configuration parameter \
ASSERT_TIMEOUT to a larger value.";

/// The cause of a panic!()
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum PanicCause {
    /// Generic cause
    Generic,
    /// Caused by a panic!()
    Panic,
    /// Caused by an assert!()
    Assert,
    /// Caused by an refute!()
    Refute,
    /// Caused by an debug_assert!()
    DebugAssert,
    /// Caused by an unreachable!()
    Unreachable,
    /// Caused by an unimplemented!()
    Unimplemented,
}

/// The kind of the method whose proof failed.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum BuiltinMethodKind {
    WriteConstant,
    MovePlace,
    IntoMemoryBlock,
    SplitMemoryBlock,
    JoinMemoryBlock,
    CopyMemoryBlock,
    ChangeUniqueRefPlace,
    DuplicateFracRef,
    Assign,
}

/// In case of verification error, this enum will contain additional information
/// required to describe the error.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum ErrorCtxt {
    /// A Viper `assert false` that encodes a Rust panic
    Panic(PanicCause),
    /// A Viper `exhale expr` that encodes the call of a Rust procedure with precondition `expr`
    ExhaleMethodPrecondition,
    /// An error when assuming method's functional specification.
    UnexpectedAssumeMethodPrecondition,
    /// An error when assuming method's functional specification.
    UnexpectedAssumeMethodPostcondition,
    /// A Viper `assert expr` that encodes the call of a Rust procedure with precondition `expr`
    AssertMethodPostcondition,
    /// A Viper `assert expr` that encodes the call of a Rust procedure with precondition `expr`
    AssertMethodPostconditionTypeInvariants,
    /// A Viper `exhale expr` that encodes the end of a Rust procedure with postcondition `expr`
    ExhaleMethodPostcondition,
    /// A generic loop invariant error.
    LoopInvariant,
    /// A Viper `exhale expr` that exhales the permissions of a loop invariant `expr`
    ExhaleLoopInvariantOnEntry,
    ExhaleLoopInvariantAfterIteration,
    /// A Viper `assert expr` that asserts the functional specification of a loop invariant `expr`
    AssertLoopInvariantOnEntry,
    AssertLoopInvariantAfterIteration,
    /// An error when assuming the loop invariant on entry.
    UnexpectedAssumeLoopInvariantOnEntry,
    /// A generic loop variant error.
    LoopVariant,
    /// Loop Variant doesn't hold on entry or after iteration
    LoopVariantOnEntry,
    LoopVariantAfterIteration,
    LoopVariantNonDecreased,
    /// If a loop needs to terminate and no loop variant is provided
    UnexpectedReachableLoop,
    /// If a call needs to terminate and it does not necessarily terminate
    UnexpectedReachableCall,
    /// Termination measure of a call might not be lower
    CallTerminationMeasureLower,
    /// The termination measure of a call might be negative
    CallTerminationMeasureNonNegative,
    /// Finding the value of the termination measure at the begin of a method unexpectedly caused an error
    UnexpectedAssignMethodTerminationMeasure,
    /// A Viper `assert false` that encodes the failure (panic) of an `assert` Rust terminator
    /// Arguments: the message of the Rust assertion
    AssertTerminator(String),
    /// A Viper `assert false` in the context of a bounds check
    BoundsCheckAssert,
    /// A Viper `assert false` in the context of a hardcoded bounds check (e.g. when we hardcode a `index`)
    /// TODO: remove this in favor of extern_spec for e.g. the stdlib `fn index(...)`
    SliceRangeBoundsCheckAssert(String),
    /// A Viper `assert false` that encodes an `abort` Rust terminator
    AbortTerminator,
    /// A Viper `assert false` that encodes an `unreachable` Rust terminator
    UnreachableTerminator,
    /// An error that should never happen
    Unexpected,
    /// An unexpected verification error happenning inside built-in method.
    UnexpectedBuiltinMethod(BuiltinMethodKind),
    /// Unexpected error when verifying a `StorageLive` statement.
    UnexpectedStorageLive,
    /// Unexpected error when verifying a `StorageDead` statement.
    UnexpectedStorageDead,
    /// An error related to a move assignment.
    MovePlace,
    /// An error related to a copy assignment.
    CopyPlace,
    /// An error related to a writing a constant.
    WritePlace,
    /// An error related to an assignment.
    Assign,
    /// A pure function definition
    #[allow(dead_code)]
    PureFunctionDefinition,
    /// A pure function call
    PureFunctionCall,
    /// An expression that encodes the value range of the result of a pure function
    PureFunctionPostconditionValueRangeOfResult,
    /// A Viper function with `false` precondition that encodes the failure (panic) of an
    /// `assert` Rust terminator in a Rust pure function.
    /// Arguments: the message of the Rust assertion
    PureFunctionAssertTerminator(String),
    /// Package a magic wand for the postcondition, at the end of a method
    PackageMagicWandForPostcondition,
    /// Apply a magic wand as a borrow expires, relevant for pledge conditions
    ApplyMagicWandOnExpiry,
    /// A diverging function call performed in a pure function
    DivergingCallInPureFunction,
    /// A Viper pure function call with `false` precondition that encodes a Rust panic in a pure function
    PanicInPureFunction(PanicCause),
    /// A Viper `assert e1 ==> e2` that encodes a weakening of the precondition
    /// of a method implementation of a trait
    AssertMethodPreconditionWeakening,
    /// A Viper `assert e1 ==> e2` that encodes a strengthening of the precondition
    /// of a method implementation of a trait.
    AssertMethodPostconditionStrengthening,
    /// A cast like `usize as u32`.
    TypeCast,
    /// A Viper `assert false` that encodes an unsupported feature.
    Unsupported(String),
    /// Failed to obtain capability by unfolding.
    Unfold,
    /// Failed to obtain capability by unfolding an union variant.
    UnfoldUnionVariant,
    /// Failed to call a procedure.
    ProcedureCall,
    /// Failed to call a drop handler.
    DropCall,
    /// Failed to encode lifetimes
    LifetimeEncoding,
    /// Failed to encode LifetimeTake
    LifetimeTake,
    /// Failed to encode LifetimeReturn
    LifetimeReturn,
    /// An error when inhaling lifetimes
    LifetimeInhale,
    /// An error when exhaling lifetimes
    LifetimeExhale,
    /// Failed to encode OpenMutRef
    OpenMutRef,
    /// Failed to encode OpenFracRef
    OpenFracRef,
    /// Failed to encode CloseMutRef
    CloseMutRef,
    /// Failed to encode CloseFracRef
    CloseFracRef,
    /// Failed to set an active variant of an union.
    SetEnumVariant,
    /// A user assumption raised an error
    Assumption,
    /// The state that fold-unfold algorithm deduced as unreachable, is actually
    /// reachable.
    UnreachableFoldingState,
}

/// The error manager
#[derive(Clone)]
pub struct ErrorManager<'tcx> {
    position_manager: PositionManager<'tcx>,
    error_contexts: FxHashMap<u64, ErrorCtxt>,
    inner_positions: FxHashMap<u64, Position>,
}

impl<'tcx> ErrorManager<'tcx> {
    pub fn new(codemap: &'tcx SourceMap) -> Self {
        ErrorManager {
            position_manager: PositionManager::new(codemap),
            error_contexts: FxHashMap::default(),
            inner_positions: FxHashMap::default(),
        }
    }

    pub fn position_manager(&self) -> &PositionManager {
        &self.position_manager
    }

    /// Register a new VIR position.
    pub fn register_span<T: Into<MultiSpan> + Debug>(
        &mut self,
        def_id: ProcedureDefId,
        span: T,
    ) -> Position {
        self.position_manager.register_span(def_id, span)
    }

    /// Duplicate an existing VIR position.
    pub fn duplicate_position(&mut self, pos: Position) -> Position {
        self.position_manager.duplicate(pos)
    }

    /// Register the ErrorCtxt on an existing VIR position.
    #[tracing::instrument(level = "trace", skip(self))]
    pub fn set_error(&mut self, pos: Position, error_ctxt: ErrorCtxt) {
        assert_ne!(
            pos,
            Position::default(),
            "Trying to register an error on a default position"
        );
        if let Some(existing_error_ctxt) = self.error_contexts.get(&pos.id()) {
            debug_assert_eq!(
                existing_error_ctxt,
                &error_ctxt,
                "An existing error context would be overwritten.\n\
                Position id: {}\n\
                Existing error context: {:?}\n\
                New error context: {:?}",
                pos.id(),
                existing_error_ctxt,
                error_ctxt
            );
        }
        self.error_contexts.insert(pos.id(), error_ctxt);
    }

    /// Creates a new position with `error_ctxt` that is linked to `pos`. This
    /// method is used for setting the surrounding context position of an
    /// expression's position.
    pub fn set_surrounding_error_context(
        &mut self,
        pos: Position,
        error_ctxt: ErrorCtxt,
    ) -> Position {
        let surrounding_position = self.duplicate_position(pos);
        self.set_error(surrounding_position, error_ctxt);
        self.inner_positions.insert(surrounding_position.id(), pos);
        surrounding_position
    }

    /// Register a new VIR position with the given ErrorCtxt.
    /// Equivalent to calling `set_error` on the output of `register_span`.
    pub fn register_error<T: Into<MultiSpan> + Debug>(
        &mut self,
        span: T,
        error_ctxt: ErrorCtxt,
        def_id: ProcedureDefId,
    ) -> Position {
        let pos = self.register_span(def_id, span);
        self.set_error(pos, error_ctxt);
        pos
    }

    pub fn get_def_id(&self, ver_error: &VerificationError) -> Option<ProcedureDefId> {
        ver_error
            .offending_pos_id
            .as_ref()
            .and_then(|id| id.parse().ok())
            .and_then(|id| self.position_manager.def_id.get(&id).copied())
    }

    #[tracing::instrument(level = "debug", skip(self))]
    pub fn translate_verification_error(&self, ver_error: &VerificationError) -> PrustiError {
        let opt_pos_id: Option<u64> = match ver_error.offending_pos_id {
            Some(ref viper_pos_id) => match viper_pos_id.parse() {
                Ok(pos_id) => Some(pos_id),
                Err(err) => {
                    return PrustiError::internal(
                        format!("unexpected Viper position '{viper_pos_id}': {err}"),
                        MultiSpan::new(),
                    );
                }
            },
            None => None,
        };
        let opt_reason_pos_id: Option<u64> = match ver_error.reason_pos_id {
            Some(ref viper_reason_pos_id) => match viper_reason_pos_id.parse() {
                Ok(reason_pos_id) => Some(reason_pos_id),
                Err(err) => {
                    return PrustiError::internal(
                        format!("unexpected Viper reason position '{viper_reason_pos_id}': {err}"),
                        MultiSpan::new(),
                    );
                }
            },
            None => None,
        };

        let opt_error_ctxts = opt_pos_id.and_then(|pos_id| self.error_contexts.get(&pos_id));
        let opt_error_span =
            opt_pos_id.and_then(|pos_id| self.position_manager.source_span.get(&pos_id));
        let opt_cause_span = opt_reason_pos_id.and_then(|reason_pos_id| {
            let res = self.position_manager.source_span.get(&reason_pos_id);
            if res.is_none() {
                debug!("Unregistered reason position: {:?}", reason_pos_id);
            }
            res
        });

        if let Some(error_ctxt) = opt_error_ctxts {
            debug_assert!(opt_error_span.is_some());
            let error_span = opt_error_span.cloned().unwrap_or_else(MultiSpan::new);
            self.translate_verification_error_with_context(
                ver_error,
                error_span,
                opt_cause_span,
                error_ctxt,
            )
        } else {
            debug!("Unregistered verification error: {:?}", ver_error);
            let error_span = if let Some(error_span) = opt_error_span {
                error_span.clone()
            } else {
                opt_cause_span.cloned().unwrap_or_else(MultiSpan::new)
            };

            match opt_pos_id {
                Some(ref pos_id) => PrustiError::internal(
                    format!(
                        "unregistered verification error: [{}; {}] {}",
                        ver_error.full_id, pos_id, ver_error.message
                    ),
                    error_span,
                )
                .set_help(ASSERTION_TIMEOUT_HELP_MESSAGE),
                None => PrustiError::internal(
                    format!(
                        "unregistered verification error: [{}] {}",
                        ver_error.full_id, ver_error.message
                    ),
                    error_span,
                )
                .set_help(ASSERTION_TIMEOUT_HELP_MESSAGE),
            }
        }
    }

    #[tracing::instrument(level = "debug", skip(self))]
    fn translate_verification_error_with_context(
        &self,
        ver_error: &VerificationError,
        error_span: MultiSpan,
        opt_cause_span: Option<&MultiSpan>,
        error_ctxt: &ErrorCtxt,
    ) -> PrustiError {
        match (ver_error.full_id.as_str(), error_ctxt) {
            ("assert.failed:assertion.false", ErrorCtxt::Panic(PanicCause::Generic)) => {
                PrustiError::verification("statement might panic", error_span)
                    .set_failing_assertion(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::Panic(PanicCause::Panic)) => {
                PrustiError::verification("panic!(..) statement might be reachable", error_span)
                    .set_failing_assertion(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::Panic(PanicCause::Assert)) |
            ("assert.failed:assertion.false", ErrorCtxt::Panic(PanicCause::DebugAssert)) => {
                    PrustiError::verification("the asserted expression might not hold", error_span)
                    .set_failing_assertion(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::Panic(PanicCause::Unreachable)) => {
                PrustiError::verification("unreachable!(..) statement might be reachable", error_span)
                    .set_failing_assertion(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::Panic(PanicCause::Unimplemented)) => {
                PrustiError::verification("unimplemented!(..) statement might be reachable", error_span)
                    .set_failing_assertion(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::AssertTerminator(ref message)) => {
                PrustiError::verification(format!("assertion might fail with \"{message}\""), error_span)
                    .set_failing_assertion(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::AbortTerminator) => {
                PrustiError::verification("statement might abort", error_span)
                    .set_failing_assertion(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::UnreachableTerminator) => {
                PrustiError::internal(
                    "unreachable code might be reachable",
                    error_span
                ).set_failing_assertion(opt_cause_span)
                    .set_help("This might be a bug in the Rust compiler.")
            }

            ("assert.failed:assertion.false", ErrorCtxt::ExhaleMethodPrecondition) => {
                PrustiError::verification("precondition might not hold.", error_span)
                    .set_failing_assertion(opt_cause_span)
            }

            ("fold.failed:assertion.false", ErrorCtxt::ExhaleMethodPrecondition) => {
                PrustiError::verification(
                    "implicit type invariant expected by the function call might not hold.",
                    error_span
                ).set_failing_assertion(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::ExhaleMethodPostcondition) => {
                PrustiError::verification("postcondition might not hold.", error_span)
                    .push_primary_span(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::ExhaleLoopInvariantOnEntry) => {
                PrustiError::verification("loop invariant might not hold in the first loop iteration.", error_span)
                    .push_primary_span(opt_cause_span)
            }

            ("fold.failed:assertion.false", ErrorCtxt::ExhaleLoopInvariantOnEntry) => {
                PrustiError::verification(
                    "implicit type invariant of a variable might not hold on loop entry.",
                    error_span
                ).push_primary_span(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::AssertLoopInvariantOnEntry) => {
                PrustiError::verification("loop invariant might not hold in the first loop iteration.", error_span)
                    .push_primary_span(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::ExhaleLoopInvariantAfterIteration) => {
                PrustiError::verification(
                    "loop invariant might not hold after a loop iteration that preserves the loop condition.",
                    error_span
                ).push_primary_span(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::AssertLoopInvariantAfterIteration) => {
                PrustiError::verification(
                    "loop invariant might not hold after a loop iteration that preserves the loop condition.",
                    error_span
                ).push_primary_span(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::DropCall) => {
                PrustiError::verification(
                    "the drop handler was called.",
                    error_span
                ).push_primary_span(opt_cause_span)
            }

            ("application.precondition:assertion.false", ErrorCtxt::PureFunctionCall) => {
                PrustiError::verification(
                    "precondition of pure function call might not hold.",
                    error_span
                ).set_failing_assertion(opt_cause_span)
            }

            ("package.failed:assertion.false", ErrorCtxt::PackageMagicWandForPostcondition) => {
                PrustiError::verification(
                    "pledge in the postcondition might not hold.",
                    error_span
                ).push_primary_span(opt_cause_span)
            }

            (
                "application.precondition:assertion.false",
                ErrorCtxt::DivergingCallInPureFunction,
            ) => {
                PrustiError::verification(
                    "diverging function call in pure function might be reachable.",
                    error_span
                ).push_primary_span(opt_cause_span)
            }

            (
                "application.precondition:assertion.false",
                ErrorCtxt::PanicInPureFunction(PanicCause::Generic),
            ) => {
                PrustiError::disabled_verification("statement in pure function might panic", error_span)
                    .push_primary_span(opt_cause_span)
            }

            (
                "application.precondition:assertion.false",
                ErrorCtxt::PanicInPureFunction(PanicCause::Panic),
            ) => {
                PrustiError::disabled_verification(
                    "panic!(..) statement in pure function might panic",
                    error_span
                ).push_primary_span(opt_cause_span)
            }

            (
                "application.precondition:assertion.false",
                ErrorCtxt::PanicInPureFunction(PanicCause::Assert),
            ) => {
                PrustiError::disabled_verification("asserted expression might not hold", error_span)
                    .set_failing_assertion(opt_cause_span)
            }

            (
                "application.precondition:assertion.false",
                ErrorCtxt::PanicInPureFunction(PanicCause::Unreachable),
            ) => {
                PrustiError::disabled_verification(
                    "unreachable!(..) statement in pure function might be reachable",
                    error_span
                ).push_primary_span(opt_cause_span)
            }

            (
                "application.precondition:assertion.false",
                ErrorCtxt::PanicInPureFunction(PanicCause::Unimplemented),
            ) => {
                PrustiError::disabled_verification(
                    "unimplemented!(..) statement in pure function might be reachable",
                    error_span
                ).push_primary_span(opt_cause_span)
            }

            ("postcondition.violated:assertion.false", ErrorCtxt::PureFunctionDefinition) |
            ("postcondition.violated:assertion.false", ErrorCtxt::PureFunctionCall) => {
                PrustiError::disabled_verification(
                    "postcondition of pure function definition might not hold",
                    error_span
                ).push_primary_span(opt_cause_span)
            }

            (
                "application.precondition:assertion.false",
                ErrorCtxt::PureFunctionAssertTerminator(ref message),
            ) => {
                PrustiError::disabled_verification(
                    format!("assertion might fail with \"{message}\""),
                    error_span
                ).set_failing_assertion(opt_cause_span)
            },

            ("application.precondition:assertion.false", ErrorCtxt::TypeCast) => {
                PrustiError::verification(
                    "value might not fit into the target type.",
                    error_span
                ).set_failing_assertion(opt_cause_span)
            }

            ("apply.failed:assertion.false", ErrorCtxt::ApplyMagicWandOnExpiry) => {
                PrustiError::verification("obligation might not hold on borrow expiry", error_span)
                    .set_failing_assertion(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::AssertMethodPostcondition) => {
                PrustiError::verification("postcondition might not hold.".to_string(), error_span)
                    .push_primary_span(opt_cause_span)
            }

            (
                "assert.failed:assertion.false",
                ErrorCtxt::AssertMethodPostconditionTypeInvariants,
            ) => {
                PrustiError::verification(
                    "type invariants might not hold at the end of the method.".to_string(),
                    error_span
                ).set_failing_assertion(opt_cause_span)
            },

            ("fold.failed:assertion.false", ErrorCtxt::PackageMagicWandForPostcondition) |
            ("fold.failed:assertion.false", ErrorCtxt::AssertMethodPostconditionTypeInvariants) => {
                PrustiError::verification(
                    "implicit type invariants might not hold at the end of the method.".to_string(),
                    error_span
                ).set_failing_assertion(opt_cause_span)
            }

            ("fold.failed:assertion.false", ErrorCtxt::CopyPlace) => {
                PrustiError::verification(
                    "the copied value may not be fully initialized.".to_string(),
                    error_span
                ).set_failing_assertion(opt_cause_span)
            }

            ("unfold.failed:insufficient.permission", ErrorCtxt::UnfoldUnionVariant) => {
                PrustiError::verification(
                    "failed to unpack the capability of union's field.".to_string(),
                    error_span
                ).set_failing_assertion(opt_cause_span)
                .set_help("check that the field was initialized.")
                .add_note("Prusti does not support yet reinterpreting memory of Rust unions' fields and allow reading only the field that was previously initialized.", None)
            }

            ("assert.failed:assertion.false", ErrorCtxt::AssertMethodPreconditionWeakening) => {
                PrustiError::verification("the method's precondition may not be a valid weakening of the trait's precondition.".to_string(), error_span)
                    .set_help("The trait's precondition should imply the implemented method's precondition.")
            }

            ("assert.failed:assertion.false", ErrorCtxt::AssertMethodPostconditionStrengthening) => {
                PrustiError::verification("the method's postcondition may not be a valid strengthening of the trait's postcondition.".to_string(), error_span)
                    .set_help("The implemented method's postcondition should imply the trait's postcondition.")
            }

            ("assert.failed:assertion.false", ErrorCtxt::BoundsCheckAssert) |
            ("application.precondition:assertion.false", ErrorCtxt::BoundsCheckAssert) => {
                PrustiError::verification(
                    "the array or slice index may be out of bounds".to_string(),
                    error_span,
                ).set_failing_assertion(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::SliceRangeBoundsCheckAssert(s)) |
            ("application.precondition:assertion.false", ErrorCtxt::SliceRangeBoundsCheckAssert(s)) => {
                PrustiError::verification(
                    s,
                    error_span,
                ).set_failing_assertion(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::Unsupported(ref reason)) => {
                PrustiError::unsupported(
                    format!("an unsupported Rust feature might be reachable: {reason}."),
                    error_span
                ).set_failing_assertion(opt_cause_span)
            }

            ("assert.failed:seq.index.length", ErrorCtxt::Panic(PanicCause::Assert)) => {
                PrustiError::verification(
                    "the sequence index may be out of bounds".to_string(),
                    error_span
                ).set_failing_assertion(opt_cause_span)
            }

            ("assert.failed:seq.index.negative", ErrorCtxt::Panic(PanicCause::Assert)) => {
                PrustiError::verification(
                    "the sequence index may be negative".to_string(),
                    error_span
                ).set_failing_assertion(opt_cause_span)
            }

            ("inhale.failed:map.key.contains", _) => {
                PrustiError::verification(
                    "the key might not be in the map".to_string(),
                    error_span
                ).set_failing_assertion(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::UnexpectedReachableLoop) => {
                PrustiError::verification(
                    "this loop might not terminate".to_string(),
                    error_span
                ).set_help("Consider attaching a loop variant at the begin of the loop with the `body_variant!` macro.\nAlternatively, remove the `#[terminates] attribute of this function, in case this is not within a ghost block.")
            }

            ("assert.failed:assertion.false", ErrorCtxt::UnexpectedReachableCall) => {
                PrustiError::verification(
                    "this function call might not terminate".to_string(),
                    error_span
                ).set_help("Consider marking the called function with `#[terminates]` or making it `#[pure]`\nAlternatively, remove the `#[terminates] attribute of this function.")
            }

            ("assert.failed:assertion.false", ErrorCtxt::CallTerminationMeasureLower) => {
                PrustiError::verification(
                    "the termination measure of this call is not necessarily lower".to_string(),
                    error_span
                )
            }

            ("assert.failed:assertion.false", ErrorCtxt::CallTerminationMeasureNonNegative) => {
                PrustiError::verification(
                    "the termination measure of this call might become negative".to_string(),
                    error_span
                )
            }

            ("assert.failed:assertion.false", ErrorCtxt::LoopVariantOnEntry) => {
                PrustiError::verification(
                    "The loop variant might not hold on entry (is lower or equal to zero)".to_string(),
                    error_span
                )
            }
            ("assert.failed:assertion.false", ErrorCtxt::LoopVariantNonDecreased) => {
                PrustiError::verification(
                    "The loop variant might not have decreased".to_string(),
                    error_span
                )
            }
            ("assert.failed:assertion.false", ErrorCtxt::LoopVariantAfterIteration) => {
                PrustiError::verification(
                    "The loop variant might go below zero while the loop continues".to_string(),
                    error_span
                )
            }

            ("refute.failed:refutation.true", ErrorCtxt::Panic(PanicCause::Refute)) => {
                PrustiError::verification(
                    "the refuted expression holds in all cases or could not be reached",
                    error_span,
                )
            }

            (full_err_id, ErrorCtxt::Unexpected) => {
                PrustiError::internal(
                    format!(
                        "unexpected verification error: [{}] {}",
                        full_err_id, ver_error.message
                    ),
                    error_span,
                ).set_failing_assertion(
                    opt_cause_span
                ).set_help(ASSERTION_TIMEOUT_HELP_MESSAGE)
            },

            _ => {
                debug!(
                    "Unhandled verification error: {:?}, context: {:?}",
                    ver_error, error_ctxt
                );
                PrustiError::internal(
                    format!(
                        "unhandled verification error: {} [{}] {:?}",
                        ver_error.message, ver_error.full_id.as_str(), error_ctxt
                    ),
                    error_span,
                ).set_failing_assertion(
                    opt_cause_span
                ).set_help(ASSERTION_TIMEOUT_HELP_MESSAGE)
            }
        }
    }
}
