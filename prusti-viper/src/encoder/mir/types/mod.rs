//! Encoder of types.

mod encoder;
mod helpers;
mod interface;

pub(crate) use self::{
    helpers::{compute_discriminant_bounds, compute_discriminant_values},
    interface::{MirTypeEncoderInterface, MirTypeEncoderState},
};

// FIXME: Remove
pub use encoder::TypeEncoder;
