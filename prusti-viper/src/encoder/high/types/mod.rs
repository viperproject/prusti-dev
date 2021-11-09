mod fields;
pub(super) mod interface;

pub(crate) use self::{
    fields::create_value_field,
    interface::{HighTypeEncoderInterface, HighTypeEncoderState},
};
