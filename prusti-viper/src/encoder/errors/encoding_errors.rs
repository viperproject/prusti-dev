use prusti_interface::PrustiError;
use rustc_span::MultiSpan;

/// An error in the encoding
#[derive(Clone, Debug)]
pub enum EncodingError {
    /// Usage of an unsupported Rust feature (e.g. dereferencing raw pointers)
    Unsupported(String, MultiSpan),
    /// Report an incorrect usage of Prusti (e.g. call an impure function in a contract)
    Incorrect(String, MultiSpan),
    /// An internal error of Prusti (e.g. failure of the fold-unfold)
    Internal(String, MultiSpan),
}

impl Into<PrustiError> for EncodingError {
    fn into(self) -> PrustiError {
        match self {
            EncodingError::Unsupported(msg, span) => {
                PrustiError::unsupported(msg, span.into())
            }
            EncodingError::Incorrect(msg, span) => {
                PrustiError::incorrect(msg, span.into())
            }
            EncodingError::Internal(msg, span) => {
                PrustiError::internal(msg, span.into())
            }
        }
    }
}

impl EncodingError {
    /// Usage of an unsupported Rust feature (e.g. dereferencing raw pointers)
    pub fn unsupported<M: ToString, S: Into<MultiSpan>>(message: M, span: S) -> Self {
        EncodingError::Unsupported(message.to_string(), span.into())
    }

    /// Report an incorrect usage of Prusti (e.g. call an impure function in a contract)
    pub fn incorrect<M: ToString, S: Into<MultiSpan>>(message: M, span: S) -> Self {
        EncodingError::Incorrect(message.to_string(), span.into())
    }

    /// An internal error of Prusti (e.g. failure of the fold-unfold)
    pub fn internal<M: ToString, S: Into<MultiSpan>>(message: M, span: S) -> Self {
        EncodingError::Internal(message.to_string(), span.into())
    }
}
