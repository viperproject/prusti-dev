// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::vir::Position;
use std::collections::HashMap;
use syntax::codemap::Span;
use syntax_pos::MultiSpan;
use uuid::Uuid;
use viper::VerificationError;
use syntax::codemap::CodeMap;
use syntax_pos::DUMMY_SP;

/// The cause of a panic!()
#[derive(Clone,Debug)]
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
#[derive(Clone,Debug)]
pub enum ErrorCtxt {
    /// A Viper `assert false` that encodes a Rust panic
    Panic(PanicCause),
    /// A Viper `exhale expr` that encodes the call of a Rust procedure with precondition `expr`
    ExhaleMethodPrecondition,
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
    UnreachableTerminator,
    /// An error that should never happen
    Unexpected,
    /// A pure function definition
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
    /// A diverging function call performed in a pure function
    DivergingCallInPureFunction,
    /// A Viper pure function call with `false` precondition that encodes a Rust panic in a pure function
    PanicInPureFunction(PanicCause),

}

/// The Rust error that will be reported from the compiler
#[derive(Clone,Debug)]
pub struct CompilerError {
    pub id: String,
    pub message: String,
    pub span: MultiSpan,
}

impl CompilerError {
    pub fn new<S1: ToString, S2: ToString>(id: S1, message: S2, span: MultiSpan) -> Self {
        CompilerError {
            id: id.to_string(),
            message: message.to_string(),
            span
        }
    }
}

/// The error manager
#[derive(Clone)]
pub struct ErrorManager<'tcx> {
    codemap: &'tcx CodeMap,
    error_ctxt: HashMap<String, (MultiSpan, ErrorCtxt)>,
}

impl<'tcx> ErrorManager<'tcx> {
    pub fn new(codemap: &'tcx CodeMap) -> Self {
        ErrorManager {
            codemap,
            error_ctxt: HashMap::new(),
        }
    }

    pub fn no_position(&mut self) -> Position {
        self.register(DUMMY_SP, ErrorCtxt::Unexpected)
    }

    pub fn register<T: Into<MultiSpan>>(&mut self, span: T, error_ctxt: ErrorCtxt) -> Position {
        let span = span.into();
        let pos_id = Uuid::new_v4().to_hyphenated().to_string();
        let lines_info = self.codemap.span_to_lines(span.primary_span().unwrap().source_callsite()).unwrap();
        let first_line_info = lines_info.lines.get(0).unwrap();
        let line = first_line_info.line_index as i32 + 1;
        let column = first_line_info.start_col.0 as i32 + 1;
        let pos = Position::new(line, column, pos_id.to_string());
        self.redefine(&pos, span, error_ctxt);
        pos
    }

    pub fn redefine(&mut self, pos: &Position, span: MultiSpan, error_ctxt: ErrorCtxt) {
        debug!("Register position: {:?}", pos);
        self.error_ctxt.insert(pos.id(), (span, error_ctxt));
    }

    pub fn translate(&self, ver_error: &VerificationError) -> CompilerError {
        let opt_error_ctxt = ver_error.pos_id.as_ref().and_then(
            |pos_id| self.error_ctxt.get(pos_id)
        );

        let (error_span, error_ctxt) = if let Some(x) = opt_error_ctxt {
            x
        } else {
            debug!("Unregistered verification error: {:?}", ver_error);

            match ver_error.pos_id {
                Some(ref pos_id) => {
                    return CompilerError::new(
                        "P1001",
                        format!(
                            "internal encoding error - unregistered verification error: [{}; {}] {}",
                            ver_error.full_id,
                            pos_id,
                            ver_error.message
                        ),
                        MultiSpan::new()
                    )
                }
                None => {
                    return CompilerError::new(
                        "P1002",
                        format!(
                            "internal encoding error - unregistered verification error: [{}] {}",
                            ver_error.full_id,
                            ver_error.message
                        ),
                        MultiSpan::new()
                    )
                }
            }
        };

        match (ver_error.full_id.as_str(), error_ctxt) {
            ("assert.failed:assertion.false", ErrorCtxt::Panic(PanicCause::Unknown)) => CompilerError::new(
                "P0001",
                "statement might panic",
                error_span.clone()
            ),

            ("assert.failed:assertion.false", ErrorCtxt::Panic(PanicCause::Panic)) => CompilerError::new(
                "P0002",
                "panic!(..) statement might panic",
                error_span.clone()
            ),

            ("assert.failed:assertion.false", ErrorCtxt::Panic(PanicCause::Assert)) => CompilerError::new(
                "P0003",
                "assert!(..) statement might not hold",
                error_span.clone()
            ),

            ("assert.failed:assertion.false", ErrorCtxt::Panic(PanicCause::Unreachable)) => CompilerError::new(
                "P0004",
                "unreachable!(..) statement might be reachable",
                error_span.clone()
            ),

            ("assert.failed:assertion.false", ErrorCtxt::Panic(PanicCause::Unimplemented)) => CompilerError::new(
                "P0005",
                "unimplemented!(..) statement might be reachable",
                error_span.clone()
            ),

            ("assert.failed:assertion.false", ErrorCtxt::AssertTerminator(ref message)) => CompilerError::new(
                "P0006",
                format!("assertion might fail with \"{}\"", message),
                error_span.clone()
            ),

            ("assert.failed:assertion.false", ErrorCtxt::AbortTerminator) => CompilerError::new(
                "P0007",
                format!("statement might abort"),
                error_span.clone()
            ),

            ("assert.failed:assertion.false", ErrorCtxt::UnreachableTerminator) => CompilerError::new(
                "P008",
                format!("unreachable code might be reachable. This might be a bug in the compiler."),
                error_span.clone()
            ),

            ("assert.failed:assertion.false", ErrorCtxt::ExhaleMethodPrecondition) => CompilerError::new(
                "P0009",
                format!("precondition might not hold."),
                error_span.clone()
            ),

            ("assert.failed:assertion.false", ErrorCtxt::ExhaleMethodPostcondition) => CompilerError::new(
                "P0010",
                format!("postcondition might not hold."),
                error_span.clone()
            ),

            ("assert.failed:assertion.false", ErrorCtxt::ExhaleLoopInvariantOnEntry) => CompilerError::new(
                "P0011",
                format!("loop invariant might not hold on entry."),
                error_span.clone()
            ),

            ("assert.failed:assertion.false", ErrorCtxt::AssertLoopInvariantOnEntry) => CompilerError::new(
                "P0012",
                format!("loop invariant might not hold on entry."),
                error_span.clone()
            ),

            ("assert.failed:assertion.false", ErrorCtxt::ExhaleLoopInvariantAfterIteration) => CompilerError::new(
                "P0013",
                format!("loop invariant might not hold at the end of a loop iteration."),
                error_span.clone()
            ),

            ("assert.failed:assertion.false", ErrorCtxt::AssertLoopInvariantAfterIteration) => CompilerError::new(
                "P0014",
                format!("loop invariant might not hold at the end of a loop iteration."),
                error_span.clone()
            ),

            ("application.precondition:assertion.false", ErrorCtxt::PureFunctionCall) => CompilerError::new(
                "P0015",
                format!("precondition of pure function call might not hold."),
                error_span.clone()
            ),

            ("package.failed:assertion.false", ErrorCtxt::PackageMagicWandForPostcondition) => CompilerError::new(
                "P0016",
                format!("pledge in the postcondition might not hold."),
                error_span.clone()
            ),

            ("application.precondition:assertion.false", ErrorCtxt::DivergingCallInPureFunction) => CompilerError::new(
                "P0017",
                format!("diverging function call in pure function might be reachable."),
                error_span.clone()
            ),

            ("application.precondition:assertion.false", ErrorCtxt::PanicInPureFunction(PanicCause::Unknown)) => CompilerError::new(
                "P0018",
                "statement in pure function might panic",
                error_span.clone()
            ),

            ("application.precondition:assertion.false", ErrorCtxt::PanicInPureFunction(PanicCause::Panic)) => CompilerError::new(
                "P0019",
                "panic!(..) statement in pure function might panic",
                error_span.clone()
            ),

            ("application.precondition:assertion.false", ErrorCtxt::PanicInPureFunction(PanicCause::Assert)) => CompilerError::new(
                "P0020",
                "assert!(..) statement in pure function might not hold",
                error_span.clone()
            ),

            ("application.precondition:assertion.false", ErrorCtxt::PanicInPureFunction(PanicCause::Unreachable)) => CompilerError::new(
                "P0021",
                "unreachable!(..) statement in pure function might be reachable",
                error_span.clone()
            ),

            ("application.precondition:assertion.false", ErrorCtxt::PanicInPureFunction(PanicCause::Unimplemented)) => CompilerError::new(
                "P0022",
                "unimplemented!(..) statement in pure function might be reachable",
                error_span.clone()
            ),

            ("postcondition.violated:assertion.false", ErrorCtxt::PureFunctionDefinition) |
            ("postcondition.violated:assertion.false", ErrorCtxt::PureFunctionCall) |
            ("postcondition.violated:assertion.false", ErrorCtxt::GenericExpression) => CompilerError::new(
                "P0023",
                "postcondition of pure function definition might not hold",
                error_span.clone()
            ),

            ("application.precondition:assertion.false", ErrorCtxt::PureFunctionAssertTerminator(ref message)) => CompilerError::new(
                "P0024",
                format!("assertion might fail with \"{}\"", message),
                error_span.clone()
            ),

            (full_err_id, ErrorCtxt::Unexpected) => CompilerError::new(
                "P1003",
                format!(
                    "internal encoding error - unexpected verification error: [{}] {}",
                    full_err_id,
                    ver_error.message
                ),
                error_span.clone()
            ),

            (full_err_id, _) => {
                debug!("Unhandled verification error: {:?}, context: {:?}", ver_error, error_ctxt);
                CompilerError::new(
                    "P1004",
                    format!(
                        "internal encoding error - unhandled verification error: {:?} [{}] {}",
                        error_ctxt,
                        full_err_id,
                        ver_error.message,
                    ),
                    error_span.clone()
                )
            },
        }
    }
}
