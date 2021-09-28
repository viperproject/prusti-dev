//! Encoder of pure functions.

mod interface;
mod encoder;
mod interpreter;

pub(crate) use interface::{PureFunctionEncoderState, PureFunctionEncoderInterface};
pub(crate) use interpreter::PureFunctionBackwardInterpreter;

