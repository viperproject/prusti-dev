use encoder::errors::PrustiError;
use prusti_interface::environment::polonius_info::PoloniusInfoError;
use syntax::codemap::Span;

/// An error in the encoding. For example, usage of unsupported Rust features.
#[derive(From)]
pub enum EncodingError {
    Procedure(ProcedureEncodingError),
    PureFunction(PureFunctionEncodingError),
}

impl From<EncodingError> for PrustiError {
    fn from(error: EncodingError) -> Self {
        match error {
            EncodingError::Procedure(ProcedureEncodingError::Internal(msg, span)) |
            EncodingError::Procedure(ProcedureEncodingError::FoldUnfold(msg, span)) => {
                PrustiError::internal(msg, span.into())
            }
            EncodingError::PureFunction(PureFunctionEncodingError::CallImpure(msg, span)) => {
                PrustiError::specification(msg, span.into())
            }
            EncodingError::Procedure(ProcedureEncodingError::Unsupported(msg, span)) => {
                PrustiError::unsupported(msg, span.into())
            }
            EncodingError::Procedure(ProcedureEncodingError::PoloniusInfo(span, err)) => {
                PrustiError::internal(
                    format!("error while processing Polonius information: {:?}", err),
                    span.into()
                )
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum ProcedureEncodingError {
    Unsupported(String, Span),
    Internal(String, Span),
    FoldUnfold(String, Span),
    PoloniusInfo(Span, PoloniusInfoError),
}

pub enum PureFunctionEncodingError {
    CallImpure(String, Span)
}
