use encoder::errors::CompilerError;
use prusti_interface::environment::polonius_info::PoloniusInfoError;
use syntax::codemap::Span;

/// An error in the encoding. For example, usage of unsupported Rust features.
#[derive(From)]
pub enum EncodingError {
    Procedure(ProcedureEncodingError),
    PureFunction(PureFunctionEncodingError),
}

impl From<EncodingError> for CompilerError {
    fn from(error: EncodingError) -> Self {
        match error {
            EncodingError::Procedure(ProcedureEncodingError::Generic(msg, span)) |
            EncodingError::PureFunction(PureFunctionEncodingError::CallImpure(msg, span)) => {
                CompilerError::new(msg, span.into())
            }
            EncodingError::Procedure(ProcedureEncodingError::PoloniusInfo(span, err)) => {
                CompilerError::new(
                    format!("Error in processing Polonius information: {:?}", err),
                    span.into()
                )
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum ProcedureEncodingError {
    Generic(String, Span),
    PoloniusInfo(Span, PoloniusInfoError),
}

pub enum PureFunctionEncodingError {
    CallImpure(String, Span)
}
