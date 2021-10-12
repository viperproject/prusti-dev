mod fields;
pub(super) mod interface;

pub(super) use self::fields::create_value_field;
pub(crate) use self::interface::{HighTypeEncoderInterface, HighTypeEncoderState};
