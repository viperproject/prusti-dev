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
}

/// The Rust error that will be reported from the compiler
#[derive(Clone, Debug)]
pub struct CompilerError {
    pub message: String,
    pub span: MultiSpan,
    pub reason_span: Option<MultiSpan>,
}

impl CompilerError {
    pub fn new<S: ToString>(message: S, span: MultiSpan, reason_span: Option<MultiSpan>) -> Self {
        CompilerError {
            message: message.to_string(),
            span,
            reason_span,
        }
    }
}

/// The error manager
#[derive(Clone)]
pub struct ErrorManager<'tcx> {
    codemap: &'tcx CodeMap,
    error_contexts: HashMap<String, (MultiSpan, ErrorCtxt)>,
}

impl<'tcx> ErrorManager<'tcx> {
    pub fn new(codemap: &'tcx CodeMap) -> Self {
        ErrorManager {
            codemap,
            error_contexts: HashMap::new(),
        }
    }

    pub fn register<T: Into<MultiSpan>>(&mut self, span: T, error_ctxt: ErrorCtxt) -> Position {
        let span = span.into();
        let pos_id = Uuid::new_v4().to_hyphenated().to_string();
        let pos = if let Some(primary_span) = span.primary_span() {
            let lines_info = self
                .codemap
                .span_to_lines(primary_span.source_callsite())
                .unwrap();
            let first_line_info = lines_info.lines.get(0).unwrap();
            let line = first_line_info.line_index as i32 + 1;
            let column = first_line_info.start_col.0 as i32 + 1;
            Position::new(line, column, pos_id.to_string())
        } else {
            Position::new(0, 0, pos_id.to_string())
        };
        self.redefine(&pos, span, error_ctxt);
        pos
    }

    pub fn redefine(&mut self, pos: &Position, span: MultiSpan, error_ctxt: ErrorCtxt) {
        debug!("Register position: {:?}", pos);
        self.error_contexts.insert(pos.id(), (span, error_ctxt));
    }

    pub fn translate(&self, ver_error: &VerificationError) -> CompilerError {
        debug!("Verification error: {:?}", ver_error);
        let pos_id = &ver_error.pos_id;
        let opt_error_ctxt = pos_id
            .as_ref()
            .and_then(|pos_id| self.error_contexts.get(pos_id));

        let (error_span, error_ctxt, reason_span) =
            if let Some((error_span, error_ctxt)) = opt_error_ctxt {
                let opt_reason_ctxt = ver_error
                    .reason_pos_id
                    .as_ref()
                    .and_then(|pos_id| self.error_contexts.get(pos_id));
                if let Some((reason_span, _)) = opt_reason_ctxt {
                    (error_span.clone(), error_ctxt, Some(reason_span.clone()))
                } else {
                    (error_span.clone(), error_ctxt, None)
                }
            } else {
                debug!("Unregistered verification error: {:?}", ver_error);

                match pos_id {
                    Some(ref pos_id) => {
                        return CompilerError::new(
                            format!(
                        "internal encoding error - unregistered verification error: [{}; {}] {}",
                        ver_error.full_id, pos_id, ver_error.message
                    ),
                            MultiSpan::new(),
                            None,
                        )
                    }
                    None => {
                        return CompilerError::new(
                            format!(
                            "internal encoding error - unregistered verification error: [{}] {}",
                            ver_error.full_id, ver_error.message
                        ),
                            MultiSpan::new(),
                            None,
                        )
                    }
                }
            };

        match (ver_error.full_id.as_str(), error_ctxt) {
            ("assert.failed:assertion.false", ErrorCtxt::Panic(PanicCause::Unknown)) => {
                CompilerError::new("statement might panic", error_span, reason_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::Panic(PanicCause::Panic)) => {
                CompilerError::new("panic!(..) statement might panic", error_span, reason_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::Panic(PanicCause::Assert)) => {
                CompilerError::new(
                    "assert!(..) statement might not hold",
                    error_span,
                    reason_span,
                )
            }

            ("assert.failed:assertion.false", ErrorCtxt::Panic(PanicCause::Unreachable)) => {
                CompilerError::new(
                    "unreachable!(..) statement might be reachable",
                    error_span,
                    reason_span,
                )
            }

            ("assert.failed:assertion.false", ErrorCtxt::Panic(PanicCause::Unimplemented)) => {
                CompilerError::new(
                    "unimplemented!(..) statement might be reachable",
                    error_span,
                    reason_span,
                )
            }

            ("assert.failed:assertion.false", ErrorCtxt::AssertTerminator(ref message)) => {
                CompilerError::new(
                    format!("assertion might fail with \"{}\"", message),
                    error_span,
                    reason_span,
                )
            }

            ("assert.failed:assertion.false", ErrorCtxt::AbortTerminator) => {
                CompilerError::new(format!("statement might abort"), error_span, reason_span)
            }

            ("assert.failed:assertion.false", ErrorCtxt::UnreachableTerminator) => {
                CompilerError::new(
                    format!(
                        "unreachable code might be reachable. This might be a bug in the compiler."
                    ),
                    error_span,
                    reason_span,
                )
            }

            ("assert.failed:assertion.false", ErrorCtxt::ExhaleMethodPrecondition) => {
                CompilerError::new(
                    format!("precondition might not hold."),
                    error_span,
                    reason_span,
                )
            }

            ("fold.failed:assertion.false", ErrorCtxt::ExhaleMethodPrecondition) => {
                CompilerError::new(
                    format!(
                        "implicit type invariant expected by the function call might not hold."
                    ),
                    error_span,
                    reason_span,
                )
            }

            ("assert.failed:assertion.false", ErrorCtxt::ExhaleMethodPostcondition) => {
                CompilerError::new(
                    format!("postcondition might not hold."),
                    error_span,
                    reason_span,
                )
            }

            ("assert.failed:assertion.false", ErrorCtxt::ExhaleLoopInvariantOnEntry) => {
                CompilerError::new(
                    format!("loop invariant might not hold on entry."),
                    error_span,
                    reason_span,
                )
            }

            ("fold.failed:assertion.false", ErrorCtxt::ExhaleLoopInvariantOnEntry) => {
                CompilerError::new(
                    format!("implicit type invariant of a variable might not hold on loop entry."),
                    error_span,
                    reason_span,
                )
            }

            ("assert.failed:assertion.false", ErrorCtxt::AssertLoopInvariantOnEntry) => {
                CompilerError::new(
                    format!("loop invariant might not hold on entry."),
                    error_span,
                    reason_span,
                )
            }

            ("assert.failed:assertion.false", ErrorCtxt::ExhaleLoopInvariantAfterIteration) => {
                CompilerError::new(
                    format!("loop invariant might not hold at the end of a loop iteration."),
                    error_span,
                    reason_span,
                )
            }

            ("assert.failed:assertion.false", ErrorCtxt::AssertLoopInvariantAfterIteration) => {
                CompilerError::new(
                    format!("loop invariant might not hold at the end of a loop iteration."),
                    error_span,
                    reason_span,
                )
            }

            ("application.precondition:assertion.false", ErrorCtxt::PureFunctionCall) => {
                CompilerError::new(
                    format!("precondition of pure function call might not hold."),
                    error_span,
                    reason_span,
                )
            }

            ("package.failed:assertion.false", ErrorCtxt::PackageMagicWandForPostcondition) => {
                CompilerError::new(
                    format!("pledge in the postcondition might not hold."),
                    error_span,
                    reason_span,
                )
            }

            (
                "application.precondition:assertion.false",
                ErrorCtxt::DivergingCallInPureFunction,
            ) => CompilerError::new(
                format!("diverging function call in pure function might be reachable."),
                error_span,
                reason_span,
            ),

            (
                "application.precondition:assertion.false",
                ErrorCtxt::PanicInPureFunction(PanicCause::Unknown),
            ) => CompilerError::new(
                "statement in pure function might panic",
                error_span,
                reason_span,
            ),

            (
                "application.precondition:assertion.false",
                ErrorCtxt::PanicInPureFunction(PanicCause::Panic),
            ) => CompilerError::new(
                "panic!(..) statement in pure function might panic",
                error_span,
                reason_span,
            ),

            (
                "application.precondition:assertion.false",
                ErrorCtxt::PanicInPureFunction(PanicCause::Assert),
            ) => CompilerError::new(
                "assert!(..) statement in pure function might not hold",
                error_span,
                reason_span,
            ),

            (
                "application.precondition:assertion.false",
                ErrorCtxt::PanicInPureFunction(PanicCause::Unreachable),
            ) => CompilerError::new(
                "unreachable!(..) statement in pure function might be reachable",
                error_span,
                reason_span,
            ),

            (
                "application.precondition:assertion.false",
                ErrorCtxt::PanicInPureFunction(PanicCause::Unimplemented),
            ) => CompilerError::new(
                "unimplemented!(..) statement in pure function might be reachable",
                error_span,
                reason_span,
            ),

            ("postcondition.violated:assertion.false", ErrorCtxt::PureFunctionDefinition)
            | ("postcondition.violated:assertion.false", ErrorCtxt::PureFunctionCall)
            | ("postcondition.violated:assertion.false", ErrorCtxt::GenericExpression) => {
                CompilerError::new(
                    "postcondition of pure function definition might not hold",
                    error_span,
                    reason_span,
                )
            }

            (
                "application.precondition:assertion.false",
                ErrorCtxt::PureFunctionAssertTerminator(ref message),
            ) => CompilerError::new(
                format!("assertion might fail with \"{}\"", message),
                error_span,
                reason_span,
            ),

            ("apply.failed:assertion.false", ErrorCtxt::ApplyMagicWandOnExpiry) => {
                CompilerError::new(
                    "obligation might not hold on borrow expiry",
                    error_span,
                    reason_span,
                )
            }

            ("assert.failed:assertion.false", ErrorCtxt::AssertMethodPostcondition) => {
                CompilerError::new(
                    format!("postcondition might not hold."),
                    error_span,
                    reason_span,
                )
            }

            (
                "assert.failed:assertion.false",
                ErrorCtxt::AssertMethodPostconditionTypeInvariants,
            ) => CompilerError::new(
                format!("type invariants might not hold at the end of the method."),
                error_span,
                reason_span,
            ),

            ("fold.failed:assertion.false", ErrorCtxt::PackageMagicWandForPostcondition)
            | ("fold.failed:assertion.false", ErrorCtxt::AssertMethodPostconditionTypeInvariants) => {
                CompilerError::new(
                    format!("implicit type invariants might not hold at the end of the method."),
                    error_span,
                    reason_span,
                )
            }

            (full_err_id, ErrorCtxt::Unexpected) => CompilerError::new(
                format!(
                    "internal encoding error - unexpected verification error: [{}] {}",
                    full_err_id, ver_error.message
                ),
                error_span,
                reason_span,
            ),

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
                    reason_span,
                )
            }
        }
    }
}
