use crate::encoder::{
    errors::SpannedEncodingError, high::to_typed::types::HighToTypedTypeEncoderInterface,
};
use vir_crate::{
    high as vir_high,
    typed::{
        self as vir_typed,
        operations::{HighToTypedType, HighToTypedTypeLowerer, TypedToHighTypeUpperer},
    },
};

impl<'v, 'tcx> HighToTypedTypeLowerer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;

    fn high_to_typed_type_type(
        &mut self,
        ty: vir_high::Type,
    ) -> Result<vir_typed::Type, Self::Error> {
        self.type_from_high_to_typed(ty)
    }

    fn high_to_typed_type_type_tuple(
        &mut self,
        ty: vir_high::ty::Tuple,
    ) -> Result<vir_typed::ty::Type, Self::Error> {
        let arguments = ty.arguments.high_to_typed_type(self)?;
        Ok(vir_typed::Type::struct_(
            self.generate_tuple_name(&arguments)?,
            arguments,
            ty.lifetimes.high_to_typed_type(self)?,
        ))
    }
}

impl<'v, 'tcx> TypedToHighTypeUpperer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;
}
