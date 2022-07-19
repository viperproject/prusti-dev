use super::interface::EncodedSequenceTypes;
use crate::encoder::{
    errors::{EncodingError, EncodingResult},
    high::types::HighTypeEncoderInterface,
    Encoder,
};
use prusti_rustc_interface::middle::ty;

pub(super) fn encode_sequence_types<'p, 'v: 'p, 'tcx: 'v>(
    encoder: &'p Encoder<'v, 'tcx>,
    sequence_ty_rs: ty::Ty<'tcx>,
) -> EncodingResult<EncodedSequenceTypes<'tcx>> {
    let (elem_ty_rs, sequence_len) = match sequence_ty_rs.kind() {
        ty::TyKind::Array(elem_ty, array_len) => {
            let len = encoder
                .const_eval_intlike(prusti_rustc_interface::middle::mir::ConstantKind::Ty(
                    *array_len,
                ))?
                .to_u64()
                .unwrap()
                .try_into()
                .unwrap();
            (*elem_ty, Some(len))
        }
        ty::TyKind::Slice(elem_ty) => (*elem_ty, None),
        ty::TyKind::Str => {
            return Err(EncodingError::unsupported(
                "Encoding of Str slice type".to_string(),
            ))
        }
        _ => unreachable!(),
    };

    let sequence_pred_type = encoder.encode_type(sequence_ty_rs)?;
    let elem_pred_type = encoder.encode_type(elem_ty_rs)?;

    Ok(EncodedSequenceTypes {
        sequence_pred_type,
        elem_pred_type,
        elem_ty_rs,
        sequence_len,
    })
}
