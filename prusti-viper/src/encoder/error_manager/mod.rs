// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::vir::Position;
use std::collections::HashMap;
use syntax::codemap::CodeMap;
use syntax_pos::MultiSpan;
use uuid::Uuid;
use viper::VerificationError;
use encoder::procedure_encoder::ProcedureEncodingError;
use encoder::pure_function_encoder::PureFunctionEncodingError;

/// The cause of a panic!()
#[derive(Clone, Debug)]
pub enum PanicCause {
    /// Unknown cause
    Unknown,
    /// Caused by a panic!()
    Panic,
    /// Caused by an assert!()
    Assert,
    /// Caused by an unreachable!()
    Unreachable,
    /// Caused by an unimplemented!()
    Unimplemented,
}

/// In case of verification error, this enum will contain additional information
/// required to describe the error.
#[derive(Clone, Debug)]
pub enum ErrorCtxt {
    /// A Viper `assert false` that encodes a Rust panic
    Panic(PanicCause),
    /// A Viper `exhale expr` that encodes the call of a Rust procedure with precondition `expr`
    ExhaleMethodPrecondition,
    /// A Viper `assert expr` that encodes the call of a Rust procedure with precondition `expr`
    AssertMethodPostcondition,
    /// A Viper `assert expr` that encodes the call of a Rust procedure with precondition `expr`
    AssertMethodPostconditionTypeInvariants,
    /// A Viper `exhale expr` that encodes the end of a Rust procedure with postcondition `expr`
    ExhaleMethodPostcondition,
    /// A Viper `exhale expr` that exhales the permissions of a loop invariant `expr`
    ExhaleLoopInvariantOnEntry,
    ExhaleLoopInvariantAfterIteration,
    /// A Viper `assert expr` that asserts the functional specification of a loop invariant `expr`
    AssertLoopInvariantOnEntry,
    AssertLoopInvariantAfterIteration,
    /// A Viper `assert false` that encodes the failure (panic) of an `assert` Rust terminator
    /// Arguments: the message of the Rust assertion
    AssertTerminator(String),
    /// A Viper `assert false` that encodes an `abort` Rust terminator
    AbortTerminator,
    /// A Viper `assert false` that encodes an `unreachable` Rust terminator
    #[allow(dead_code)]
    UnreachableTerminator,
    /// An error that should never happen
    Unexpected,
    /// A pure function definition
    #[allow(dead_code)]
    PureFunctionDefinition,
    /// A pure function call
    PureFunctionCall,
    /// A stub pure function call
    StubPureFunctionCall,
    /// An expression that encodes the value range of the result of a pure function
    PureFunctionPostconditionValueRangeOfResult,
    /// A Viper function with `false` precondition that encodes the failure (panic) of an
    /// `assert` Rust terminator in a Rust pure function.
    /// Arguments: the message of the Rust assertion
    PureFunctionAssertTerminator(String),
    /// A generic expression
    GenericExpression,
    /// A generic statement
    GenericStatement,
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
    AssertMethodPreconditionWeakening(MultiSpan),
    /// A Viper `assert e1 ==> e2` that encodes a strengthening of the precondition
    /// of a method implementation of a trait.
    AssertMethodPostconditionStrengthening(MultiSpan),
    /// A Viper `assert false` that encodes an unsupported reason
    Unsupported(String),
}

/// An error in the encoding. For example, usage of unsupported Rust features.
#[derive(From)]
pub enum EncodingError {
    Procedure(ProcedureEncodingError),
    PureFunction(PureFunctionEncodingError),
}

/// The Rust error that will be reported from the compiler
#[derive(Clone, Debug)]
pub struct CompilerError {
    pub message: String,
    pub span: MultiSpan,
    pub help: Option<String>,
    pub note: Option<(String, MultiSpan)>,
}

impl CompilerError {
    pub fn new<S: ToString>(message: S, span: MultiSpan) -> Self {
        CompilerError {
            message: message.to_string(),
            span,
            help: None,
            note: None,
        }
    }

    pub fn set_help<S: ToString>(mut self, message: S) -> Self {
        self.help = Some(message.to_string());
        self
    }

    /// Set the span of the failing assertion expression.
    ///
    /// Note: this is a noop if `opt_span` is None
    pub fn set_failing_assertion(mut self, opt_span: Option<&MultiSpan>) -> Self {
        if let Some(span) = opt_span {
            self.note = Some(("the failing assertion is here".to_string(), span.clone()));
        }
        self
    }

    /// Convert the original error span to a note, and add a new error span.
    ///
    /// Note: this is a noop if `opt_span` is None
    pub fn push_primary_span(mut self, opt_span: Option<&MultiSpan>) -> Self {
        if let Some(span) = opt_span {
            self.note = Some(("the error originates here".to_string(), self.span));
            self.span = span.clone();
        }
        self
    }
}

/// The error manager
#[derive(Clone)]
pub struct ErrorManager<'tcx> {
    codemap: &'tcx CodeMap,
    source_span: HashMap<String, MultiSpan>,
    error_contexts: HashMap<String, ErrorCtxt>,
}

impl<'tcx> ErrorManager<'tcx> {
    pub fn new(codemap: &'tcx CodeMap) -> Self {
        ErrorManager {
            codemap,
            source_span: HashMap::new(),
            error_contexts: HashMap::new(),
        }
    }

    pub fn register<T: Into<MultiSpan>>(&mut self, span: T, error_ctxt: ErrorCtxt) -> Position {
        let pos = self.register_span(span);
        self.register_error(&pos, error_ctxt);
        pos
    }

    pub fn register_span<T: Into<MultiSpan>>(&mut self, span: T) -> Position {
        let span = span.into();
        let pos_id = Uuid::new_v4().to_hyphenated().to_string();
        debug!("Register position {:?} at span {:?}", pos_id, span);
        let pos = if let Some(primary_span) = span.primary_span() {
            let lines_info = self
                .codemap
                .span_to_lines(primary_span.source_callsite())
                .unwrap();
            let first_line_info = lines_info.lines.get(0).unwrap();
            let line = first_line_info.line_index as i32 + 1;
            let column = first_line_info.start_col.0 as i32 + 1;
            Position::new(line, column, pos_id.clone())
        } else {
            Position::new(0, 0, pos_id.clone())
        };
        self.source_span.insert(pos_id, span);
        pos
    }

    pub fn register_error(&mut self, pos: &Position, error_ctxt: ErrorCtxt) {
        debug!("Register error at: {:?}", pos.id());
        self.error_contexts.insert(pos.id(), error_ctxt);
    }

    pub fn translate_verification_error(&self, ver_error: &VerificationError) -> CompilerError {
        debug!("Verification error: {:?}", ver_error);
        let pos_id = &ver_error.pos_id;
        let opt_error_span = pos_id
            .as_ref()
            .and_then(|pos_id| self.source_span.get(pos_id));
        let opt_cause_span = ver_error
            .reason_pos_id
            .as_ref()
            .and_then(|reason_pos_id| {
                let res = self.source_span.get(reason_pos_id);
                if res.is_none() {
                    debug!("Unregistered reason position: {:?}", reason_pos_id);
                }
                res
            });

        let opt_error_ctxt = pos_id
            .as_ref()
            .and_then(|pos_id| self.error_contexts.get(pos_id));

        let (error_span, error_ctxt) = if let Some(error_ctxt) = opt_error_ctxt {
            debug_assert!(opt_error_span.is_some());
            let error_span = opt_error_span.cloned().unwrap_or_else(|| MultiSpan::new());
            (error_span, error_ctxt)
        } else {
            debug!("Unregistered verification error: {:?}", ver_error);
            let error_span = if let Some(error_span) = opt_error_span {
                error_span.clone()
            } else {
                opt_cause_span.cloned().unwrap_or_else(|| MultiSpan::new())
            };

            match pos_id {
                Some(ref pos_id) => {
                    return CompilerError::new(
                        format!(
                            "internal encoding error - unregistered verification error: [{}; {}] {}",
                            ver_error.full_id, pos_id, ver_error.message
                        ),
                        error_span
                    ).set_help(
                        "This could be caused by too small assertion timeout. \
                        Try increasing it by setting the configuration parameter \
                        ASSERT_TIMEOUT to a larger value."
                    )
                }
                None => {
                    return CompilerError::new(
                        format!(
                            "internal encoding error - unregistered verification error: [{}] {}",
                            ver_error.full_id, ver_error.message
                        ),
                        error_span
                    ).set_help(
                        "This could be caused by too small assertion timeout. \
                        Try increasing it by setting the configuration parameter \
                        ASSERT_TIMEOUT to a larger value."
                    )
                }
            }
        };

        match (ver_error.full_id.as_str(), error_ctxt) {
            ("assert.failed:assertion.false", ErrorCtxt::Panic(PanicCause::Unknown)) => {
                CompilerError::new("statement might panic", error_span)
                    .set_failing_assertion(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::Panic(PanicCause::Panic)) => {
                CompilerError::new("panic!(..) statement might panic", error_span)
                    .set_failing_assertion(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::Panic(PanicCause::Assert)) => {
                CompilerError::new("the asserted expression might not hold", error_span)
                    .set_failing_assertion(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::Panic(PanicCause::Unreachable)) => {
                CompilerError::new("unreachable!(..) statement might be reachable", error_span)
                    .set_failing_assertion(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::Panic(PanicCause::Unimplemented)) => {
                CompilerError::new("unimplemented!(..) statement might be reachable", error_span)
                    .set_failing_assertion(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::AssertTerminator(ref message)) => {
                CompilerError::new(format!("assertion might fail with \"{}\"", message), error_span)
                    .set_failing_assertion(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::AbortTerminator) => {
                CompilerError::new(format!("statement might abort"), error_span)
                    .set_failing_assertion(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::UnreachableTerminator) => {
                CompilerError::new(
                    format!(
                        "unreachable code might be reachable. This might be a bug in the compiler."
                    ),
                    error_span
                ).set_failing_assertion(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::ExhaleMethodPrecondition) => {
                CompilerError::new(format!("precondition might not hold."), error_span)
                    .set_failing_assertion(opt_cause_span)
            }

            ("fold.failed:assertion.false", ErrorCtxt::ExhaleMethodPrecondition) => {
                CompilerError::new(
                    format!(
                        "implicit type invariant expected by the function call might not hold."
                    ),
                    error_span
                ).set_failing_assertion(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::ExhaleMethodPostcondition) => {
                CompilerError::new(format!("postcondition might not hold."), error_span)
                    .push_primary_span(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::ExhaleLoopInvariantOnEntry) => {
                CompilerError::new(format!("loop invariant might not hold on entry."), error_span)
                    .push_primary_span(opt_cause_span)
            }

            ("fold.failed:assertion.false", ErrorCtxt::ExhaleLoopInvariantOnEntry) => {
                CompilerError::new(
                    format!("implicit type invariant of a variable might not hold on loop entry."),
                    error_span
                ).push_primary_span(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::AssertLoopInvariantOnEntry) => {
                CompilerError::new(format!("loop invariant might not hold on entry."), error_span)
                    .push_primary_span(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::ExhaleLoopInvariantAfterIteration) => {
                CompilerError::new(
                    format!("loop invariant might not hold at the end of a loop iteration."),
                    error_span
                ).push_primary_span(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::AssertLoopInvariantAfterIteration) => {
                CompilerError::new(
                    format!("loop invariant might not hold at the end of a loop iteration."),
                    error_span
                ).push_primary_span(opt_cause_span)
            }

            ("application.precondition:assertion.false", ErrorCtxt::PureFunctionCall) => {
                CompilerError::new(
                    format!("precondition of pure function call might not hold."),
                    error_span
                ).set_failing_assertion(opt_cause_span)
            }

            ("application.precondition:assertion.false", ErrorCtxt::StubPureFunctionCall) => {
                CompilerError::new(
                    format!("use of impure function might be reachable."),
                    error_span
                ).set_failing_assertion(opt_cause_span)
                    .set_help("Functions called from assertions should be marked as pure.")
            }

            ("package.failed:assertion.false", ErrorCtxt::PackageMagicWandForPostcondition) => {
                CompilerError::new(
                    format!("pledge in the postcondition might not hold."),
                    error_span
                ).push_primary_span(opt_cause_span)
            }

            (
                "application.precondition:assertion.false",
                ErrorCtxt::DivergingCallInPureFunction,
            ) => {
                CompilerError::new(
                    format!("diverging function call in pure function might be reachable."),
                    error_span
                ).push_primary_span(opt_cause_span)
            }

            (
                "application.precondition:assertion.false",
                ErrorCtxt::PanicInPureFunction(PanicCause::Unknown),
            ) => {
                CompilerError::new("statement in pure function might panic", error_span)
                    .push_primary_span(opt_cause_span)
            }

            (
                "application.precondition:assertion.false",
                ErrorCtxt::PanicInPureFunction(PanicCause::Panic),
            ) => {
                CompilerError::new("panic!(..) statement in pure function might panic", error_span)
                    .push_primary_span(opt_cause_span)
            }

            (
                "application.precondition:assertion.false",
                ErrorCtxt::PanicInPureFunction(PanicCause::Assert),
            ) => {
                CompilerError::new("asserted expression might not hold", error_span)
                    .set_failing_assertion(opt_cause_span)
            }

            (
                "application.precondition:assertion.false",
                ErrorCtxt::PanicInPureFunction(PanicCause::Unreachable),
            ) => {
                CompilerError::new(
                    "unreachable!(..) statement in pure function might be reachable",
                    error_span
                ).push_primary_span(opt_cause_span)
            }

            (
                "application.precondition:assertion.false",
                ErrorCtxt::PanicInPureFunction(PanicCause::Unimplemented),
            ) => {
                CompilerError::new(
                    "unimplemented!(..) statement in pure function might be reachable",
                    error_span
                ).push_primary_span(opt_cause_span)
            }

            ("postcondition.violated:assertion.false", ErrorCtxt::PureFunctionDefinition) |
            ("postcondition.violated:assertion.false", ErrorCtxt::PureFunctionCall) |
            ("postcondition.violated:assertion.false", ErrorCtxt::GenericExpression) => {
                CompilerError::new(
                    "postcondition of pure function definition might not hold",
                    error_span
                ).push_primary_span(opt_cause_span)
            }

            (
                "application.precondition:assertion.false",
                ErrorCtxt::PureFunctionAssertTerminator(ref message),
            ) => {
                CompilerError::new(
                    format!("assertion might fail with \"{}\"", message),
                    error_span
                ).set_failing_assertion(opt_cause_span)
            },

            ("apply.failed:assertion.false", ErrorCtxt::ApplyMagicWandOnExpiry) => {
                CompilerError::new("obligation might not hold on borrow expiry", error_span)
                    .set_failing_assertion(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::AssertMethodPostcondition) => {
                CompilerError::new(format!("postcondition might not hold."), error_span)
                    .push_primary_span(opt_cause_span)
            }

            (
                "assert.failed:assertion.false",
                ErrorCtxt::AssertMethodPostconditionTypeInvariants,
            ) => {
                CompilerError::new(
                    format!("type invariants might not hold at the end of the method."),
                    error_span
                ).set_failing_assertion(opt_cause_span)
            },

            ("fold.failed:assertion.false", ErrorCtxt::PackageMagicWandForPostcondition) |
            ("fold.failed:assertion.false", ErrorCtxt::AssertMethodPostconditionTypeInvariants) => {
                CompilerError::new(
                    format!("implicit type invariants might not hold at the end of the method."),
                    error_span
                ).set_failing_assertion(opt_cause_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::AssertMethodPreconditionWeakening(impl_span)) => {
                CompilerError::new(format!("the method's precondition may not be a valid weakening of the trait's precondition."), error_span)
                    //.push_primary_span(opt_cause_span)
                    .push_primary_span(Some(&impl_span))
                    .set_help("The trait's precondition should imply the implemented method's precondition.")
            }

            ("assert.failed:assertion.false", ErrorCtxt::AssertMethodPostconditionStrengthening(impl_span)) => {
                CompilerError::new(format!("the method's postcondition may not be a valid strengthening of the trait's postcondition."), error_span)
                    //.push_primary_span(opt_cause_span)
                    .push_primary_span(Some(&impl_span))
                    .set_help("The implemented method's postcondition should imply the trait's postcondition.")
            }

            ("assert.failed:assertion.false", ErrorCtxt::Unsupported(ref reason)) => {
                CompilerError::new(
                    format!("a statement unsupported by Prusti may be reached: {}.", reason),
                    error_span
                ).set_failing_assertion(opt_cause_span)
            }

            (full_err_id, ErrorCtxt::Unexpected) => {
                CompilerError::new(
                    format!(
                        "internal encoding error - unexpected verification error: [{}] {}",
                        full_err_id, ver_error.message
                    ),
                    error_span,
                ).set_failing_assertion(
                    opt_cause_span
                ).set_help(
                    "This could be caused by too small assertion timeout. \
                    Try increasing it by setting the configuration parameter \
                    ASSERT_TIMEOUT to a larger value."
                )
            },

            (full_err_id, _) => {
                debug!(
                    "Unhandled verification error: {:?}, context: {:?}",
                    ver_error, error_ctxt
                );
                CompilerError::new(
                    format!(
                        "internal encoding error - unhandled verification error: {:?} [{}] {}",
                        error_ctxt, full_err_id, ver_error.message,
                    ),
                    error_span,
                ).set_failing_assertion(
                    opt_cause_span
                ).set_help(
                    "This could be caused by too small assertion timeout. \
                    Try increasing it by setting the configuration parameter \
                    ASSERT_TIMEOUT to a larger value."
                )
            }
        }
    }

    pub fn translate_encoding_error(&self, error: EncodingError) -> CompilerError {
        match error {
            EncodingError::Procedure(ProcedureEncodingError::UnsupportedLoanInLoop(msg, span)) |
            EncodingError::PureFunction(PureFunctionEncodingError::CallImpure(msg, span)) => {
                CompilerError::new(msg, span.into())
            }
        }
    }
}
