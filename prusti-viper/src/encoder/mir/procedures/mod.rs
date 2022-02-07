//! Encoder of procedures with explicit lifetimes.

mod encoder;
mod interface;

pub(crate) use self::interface::{MirProcedureEncoderInterface, MirProcedureEncoderState};
