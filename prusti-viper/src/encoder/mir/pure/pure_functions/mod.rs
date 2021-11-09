//! Encoder of pure functions.

mod encoder;
mod interface;
mod interpreter;
mod new_encoder;

pub(crate) use interface::{PureFunctionEncoderInterface, PureFunctionEncoderState};
pub(crate) use interpreter::PureFunctionBackwardInterpreter;
