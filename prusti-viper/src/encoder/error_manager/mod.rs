use encoder::vir::Position;
use std::collections::HashMap;
use syntax::codemap::Span;
use syntax_pos::MultiSpan;
use uuid::Uuid;
use viper::VerificationError;
use syntax::codemap::CodeMap;

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

/// In case of verification error, this enum will contain all the information (span, ...)
/// required to report the error in the compiler.
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
    /// A pure function call
    PureFunctionCall,
    /// Package a magic wand for the postcondition, at the end of a method
    PackageMagicWandForPostcondition,
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
    error_contexts: HashMap<String, (Span, ErrorCtxt)>,
}

impl<'tcx> ErrorManager<'tcx> {
    pub fn new(codemap: &'tcx CodeMap) -> Self {
        ErrorManager {
            codemap,
            error_contexts: HashMap::new(),
        }
    }

    pub fn register(&mut self, span: Span, error_ctx: ErrorCtxt) -> Position {
        let pos_id = Uuid::new_v4().to_hyphenated().to_string();
        self.error_contexts.insert(pos_id.to_string(), (span, error_ctx));
        let lines_info = self.codemap.span_to_lines(span.source_callsite()).unwrap();
        let first_line_info = lines_info.lines.get(0).unwrap();
        let line = first_line_info.line_index as i32 + 1;
        let column = first_line_info.start_col.0 as i32 + 1;
        let pos = Position::new(line, column, pos_id.to_string());
        debug!("Register position: {:?}", pos);
        pos
    }

    pub fn translate(&self, ver_error: &VerificationError) -> CompilerError {
        let opt_error_ctx = ver_error.pos_id.as_ref().and_then(
            |pos_id| self.error_contexts.get(pos_id)
        );

        let (error_span, error_ctx) = if let Some(x) = opt_error_ctx {
            x
        } else {
            debug!("Unregistered verification error: {:?}", ver_error);

            match ver_error.pos_id {
                Some(ref pos_id) => {
                    return CompilerError::new(
                        "P0001",
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
                        "P0002",
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

        match (ver_error.full_id.as_str(), error_ctx) {
            ("assert.failed:assertion.false", ErrorCtxt::Panic(PanicCause::Unknown)) => CompilerError::new(
                "P0003",
                "statement might panic",
                MultiSpan::from_span(*error_span)
            ),

            ("assert.failed:assertion.false", ErrorCtxt::Panic(PanicCause::Panic)) => CompilerError::new(
                "P0004",
                "panic!(..) statement might panic",
                MultiSpan::from_span(*error_span)
            ),

            ("assert.failed:assertion.false", ErrorCtxt::Panic(PanicCause::Assert)) => CompilerError::new(
                "P0005",
                "assert!(..) statement might not hold",
                MultiSpan::from_span(*error_span)
            ),

            ("assert.failed:assertion.false", ErrorCtxt::Panic(PanicCause::Unreachable)) => CompilerError::new(
                "P0006",
                "unreachable!(..) statement might be reachable",
                MultiSpan::from_span(*error_span)
            ),

            ("assert.failed:assertion.false", ErrorCtxt::AssertTerminator(ref message)) => CompilerError::new(
                "P0007",
                format!("assertion might fail with \"{}\"", message),
                MultiSpan::from_span(*error_span)
            ),

            ("assert.failed:assertion.false", ErrorCtxt::Panic(PanicCause::Unimplemented)) => CompilerError::new(
                "P0008",
                "unimplemented!(..) statement might be reachable",
                MultiSpan::from_span(*error_span)
            ),

            ("assert.failed:assertion.false", ErrorCtxt::AbortTerminator) => CompilerError::new(
                "P0009",
                format!("statement might abort"),
                MultiSpan::from_span(*error_span)
            ),

            ("assert.failed:assertion.false", ErrorCtxt::UnreachableTerminator) => CompilerError::new(
                "P0010",
                format!("unreachable code might be reachable. This might be a bug in the compiler."),
                MultiSpan::from_span(*error_span)
            ),

            ("assert.failed:assertion.false", ErrorCtxt::ExhaleMethodPrecondition) => CompilerError::new(
                "P0011",
                format!("precondition might not hold."),
                MultiSpan::from_span(*error_span)
            ),

            ("assert.failed:assertion.false", ErrorCtxt::ExhaleMethodPostcondition) => CompilerError::new(
                "P0012",
                format!("postcondition might not hold."),
                MultiSpan::from_span(*error_span)
            ),

            ("assert.failed:assertion.false", ErrorCtxt::ExhaleLoopInvariantOnEntry) => CompilerError::new(
                "P0013",
                format!("loop invariant might not hold on entry."),
                MultiSpan::from_span(*error_span)
            ),

            ("assert.failed:assertion.false", ErrorCtxt::AssertLoopInvariantOnEntry) => CompilerError::new(
                "P0014",
                format!("loop invariant might not hold on entry."),
                MultiSpan::from_span(*error_span)
            ),

            ("assert.failed:assertion.false", ErrorCtxt::ExhaleLoopInvariantAfterIteration) => CompilerError::new(
                "P0015",
                format!("loop invariant might not hold at the end of a loop iteration."),
                MultiSpan::from_span(*error_span)
            ),

            ("assert.failed:assertion.false", ErrorCtxt::AssertLoopInvariantAfterIteration) => CompilerError::new(
                "P0016",
                format!("loop invariant might not hold at the end of a loop iteration."),
                MultiSpan::from_span(*error_span)
            ),

            ("application.precondition:assertion.false", ErrorCtxt::PureFunctionCall) => CompilerError::new(
                "P0017",
                format!("precondition of pure function call might not hold."),
                MultiSpan::from_span(*error_span)
            ),

            ("package.failed:assertion.false", ErrorCtxt::PackageMagicWandForPostcondition) => CompilerError::new(
                "P0018",
                format!("pledge in the postcondition might not hold."),
                MultiSpan::from_span(*error_span)
            ),

            (full_err_id, ErrorCtxt::Unexpected) => CompilerError::new(
                "P0019",
                format!(
                    "internal encoding error - unexpected verification error: [{}] {}",
                    full_err_id,
                    ver_error.message
                ),
                MultiSpan::from_span(*error_span)
            ),

            (full_err_id, _) => {
                debug!("Unhandled verification error: {:?}, context: {:?}", ver_error, error_ctx);
                CompilerError::new(
                    "P0020",
                    format!(
                        "internal encoding error - unhandled verification error: [{}] {}",
                        full_err_id,
                        ver_error.message
                    ),
                    MultiSpan::from_span(*error_span)
                )
            },
        }
    }
}
