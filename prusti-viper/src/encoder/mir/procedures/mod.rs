//! Encoder of procedures with explicit lifetimes.

mod encoder;
mod interface;
mod passes;

pub(crate) use self::interface::{MirProcedureEncoderInterface, MirProcedureEncoderState};
