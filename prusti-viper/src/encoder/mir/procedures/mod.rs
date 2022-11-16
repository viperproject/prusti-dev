//! Encoder of procedures with explicit lifetimes.

pub mod encoder;
mod interface;
mod passes;

pub(crate) use self::interface::{MirProcedureEncoderInterface, MirProcedureEncoderState};
