use encoder::vir::PosId;
use std::collections::HashMap;
use syntax::codemap::Span;
use syntax_pos::MultiSpan;
use uuid::Uuid;
use viper::VerificationError;

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
}

/// In case of verification error, this enum will contain all the information (span, ...)
/// required to report the error in the compiler.
#[derive(Clone,Debug)]
pub enum ErrorCtxt {
    /// A Viper `assert false` that encodes a Rust panic
    /// Arguments: the span of the statement that might panic
    Panic(Span, PanicCause),
    /// A Viper `exhale expr` that encodes the call of a Rust procedure wit precondition `expr`
    ExhalePrecondition(),
    /// A Viper `exhale expr` that encodes the end of a Rust procedure wit postcondition `expr`
    ExhalePostcondition(),
    /// A Viper `assert false` that encodes the failure (panic) of an `assert` Rust terminator
    /// Arguments: the span of the statement that might fail, the message of the Rust assertion
    AssertTerminator(Span, String),
    /// A Viper `assert false` that encodes an `abort` Rust terminator
    AbortTerminator(Span),
    /// A Viper `assert false` that encodes an `unreachable` Rust terminator
    UnreachableTerminator(Span),
    /// An error that should never happen
    Unexpected(),
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
#[derive(Clone,Debug)]
pub struct ErrorManager {
    error_contexts: HashMap<String, ErrorCtxt>,
}

impl ErrorManager {
    pub fn new() -> Self {
        ErrorManager {
            error_contexts: HashMap::new(),
        }
    }

    pub fn register(&mut self, error_ctx: ErrorCtxt) -> PosId {
        let pos_id = Uuid::new_v4().hyphenated().to_string();
        self.error_contexts.insert(pos_id.clone(), error_ctx);
        PosId::new(pos_id)
    }

    pub fn translate(&self, ver_error: &VerificationError) -> CompilerError {
        let opt_error_ctx = self.error_contexts.get(&ver_error.pos_id);

        let error_ctx = if let Some(x) = opt_error_ctx {
            x
        } else {
            error!("Unregistered verification error: {:?}", ver_error);
            return CompilerError::new(
                ver_error.full_id.clone(),
                format!("Unregistered verification error: {}", ver_error.message),
                MultiSpan::new()
            )
        };

        match (ver_error.full_id.as_str(), error_ctx) {
            ("assert.failed:assertion.false", ErrorCtxt::Panic(span, PanicCause::Unknown)) => CompilerError::new(
                "P0001",
                "statement might panic",
                MultiSpan::from_span(*span)
            ),

            ("assert.failed:assertion.false", ErrorCtxt::Panic(span, PanicCause::Panic)) => CompilerError::new(
                "P0002",
                "panic!(..) statement might panic",
                MultiSpan::from_span(*span)
            ),

            ("assert.failed:assertion.false", ErrorCtxt::Panic(span, PanicCause::Assert)) => CompilerError::new(
                "P0003",
                "assert!(..) statement might not hold",
                MultiSpan::from_span(*span)
            ),

            ("assert.failed:assertion.false", ErrorCtxt::Panic(span, PanicCause::Unreachable)) => CompilerError::new(
                "P0004",
                "unreachable!(..) statement might be reachable",
                MultiSpan::from_span(*span)
            ),

            ("assert.failed:assertion.false", ErrorCtxt::AssertTerminator(span, ref message)) => CompilerError::new(
                "P0005",
                format!("assertion might fail with \"{}\"", message),
                MultiSpan::from_span(*span)
            ),

            ("assert.failed:assertion.false", ErrorCtxt::AbortTerminator(span)) => CompilerError::new(
                "P????",
                format!("statement might abort"),
                MultiSpan::from_span(*span)
            ),

            ("assert.failed:assertion.false", ErrorCtxt::UnreachableTerminator(span)) => CompilerError::new(
                "P????",
                format!("unreachable code might be reachable. This might be a bug in the compiler."),
                MultiSpan::from_span(*span)
            ),

            (full_err_id, ErrorCtxt::Unexpected()) => CompilerError::new(
                full_err_id,
                format!("unexpected verification error ({})", ver_error.message),
                MultiSpan::new()
            ),

            (full_err_id, _) => {
                error!("Unhandled verification error: {:?}, context: {:?}", ver_error, error_ctx);
                CompilerError::new(
                    full_err_id,
                    format!("Unhandled verification error ({})", ver_error.message),
                    MultiSpan::new()
                )
            },
        }
    }
}
