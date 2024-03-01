//! Encoder of types.

mod const_parameters;
mod encoder;
mod helpers;
mod interface;
mod lifetimes;

pub(crate) use self::{
    helpers::{compute_discriminant_bounds, compute_discriminant_values},
    interface::{MirTypeEncoderInterface, MirTypeEncoderState},
};

// FIXME: Remove
pub use encoder::TypeEncoder;
