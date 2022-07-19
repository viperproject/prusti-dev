use crate::encoder::{
    errors::EncodingResult, high::lower::IntoPolymorphic,
    mir::generics::MirGenericsEncoderInterface,
};
use prusti_rustc_interface::{hir::def_id::DefId, middle::ty::subst::SubstsRef};
use vir_crate::polymorphic as vir_poly;

pub(crate) trait HighGenericsEncoderInterface<'tcx> {
    fn encode_generic_parameters(&self, def_id: DefId) -> EncodingResult<Vec<vir_poly::TypeVar>>;
    fn encode_generic_arguments(
        &self,
        def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> EncodingResult<Vec<vir_poly::Type>>;
}

impl<'v, 'tcx: 'v> HighGenericsEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn encode_generic_parameters(&self, def_id: DefId) -> EncodingResult<Vec<vir_poly::TypeVar>> {
        let type_parameters = self.encode_generic_parameters_high(def_id)?;
        Ok(type_parameters.lower(self))
    }
    fn encode_generic_arguments(
        &self,
        def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> EncodingResult<Vec<vir_poly::Type>> {
        let type_arguments = self.encode_generic_arguments_high(def_id, substs)?;
        Ok(type_arguments.lower(self))
    }
}
