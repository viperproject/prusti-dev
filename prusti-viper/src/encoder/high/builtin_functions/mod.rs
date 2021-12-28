//! Encoder of builtin pure functions.

mod encoder;
mod interface;

pub(crate) use interface::{
    BuiltinFunctionHighKind, HighBuiltinFunctionEncoderInterface, HighBuiltinFunctionEncoderState,
};
