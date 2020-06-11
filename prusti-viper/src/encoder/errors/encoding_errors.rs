use encoder::errors::PrustiError;
use prusti_interface::environment::polonius_info::PoloniusInfoError;
use syntax_pos::MultiSpan;

/// An error in the encoding
#[derive(Clone, Debug)]
pub enum EncodingError {
    /// Usage of an unsupported Rust feature
    Unsupported(String, MultiSpan),
    /// An error in the specification provided by the user
    Specification(String, MultiSpan),
    /// An internal error of Prusti
    Internal(String, MultiSpan),
}

impl Into<PrustiError> for EncodingError {
    fn into(self) -> PrustiError {
        match self {
            EncodingError::Unsupported(msg, span) => {
                PrustiError::unsupported(msg, span.into())
            }
            EncodingError::Specification(msg, span) => {
                PrustiError::specification(msg, span.into())
            }
            EncodingError::Internal(msg, span) => {
                PrustiError::internal(msg, span.into())
            }
        }
    }
}

impl EncodingError {
    pub fn unsupported<M: ToString, S: Into<MultiSpan>>(message: M, span: S) -> Self {
        EncodingError::Unsupported(message.to_string(), span.into())
    }

    pub fn specification<M: ToString, S: Into<MultiSpan>>(message: M, span: S) -> Self {
        EncodingError::Specification(message.to_string(), span.into())
    }

    pub fn internal<M: ToString, S: Into<MultiSpan>>(message: M, span: S) -> Self {
        EncodingError::Internal(message.to_string(), span.into())
    }
}
