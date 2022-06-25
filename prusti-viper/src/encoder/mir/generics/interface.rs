use crate::encoder::{errors::EncodingResult, mir::types::MirTypeEncoderInterface};

use prusti_rustc_interface::{
    hir::def_id::DefId,
    middle::ty::{self, subst::SubstsRef},
    span::symbol::Symbol,
};
use vir_crate::high::{self as vir_high};

pub(crate) trait MirGenericsEncoderInterface<'tcx> {
    /// For a function specified with the `def_id`, encode the full list list of
    /// its generic parameters.
    fn encode_generic_parameters_high(
        &self,
        def_id: DefId,
    ) -> EncodingResult<Vec<vir_high::ty::TypeVar>>;
    /// For a function specified with the `def_id`, encode the list of type
    /// arguments to be applied for each of generic parameters returned by
    /// `encode_generic_parameters`.
    fn encode_generic_arguments_high(
        &self,
        def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> EncodingResult<Vec<vir_high::ty::Type>>;
    fn encode_param(&self, name: Symbol, index: u32) -> vir_high::ty::TypeVar;
}

impl<'v, 'tcx: 'v> MirGenericsEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn encode_generic_parameters_high(
        &self,
        def_id: DefId,
    ) -> EncodingResult<Vec<vir_high::ty::TypeVar>> {
        let generics = self.env().tcx().generics_of(def_id);
        let mut parameters = if let Some(parent) = generics.parent {
            self.encode_generic_parameters_high(parent)?
        } else {
            Vec::new()
        };
        for generic in &generics.params {
            let name = generic.name;
            let index = generics.param_def_id_to_index[&generic.def_id];
            parameters.push(self.encode_param(name, index));
        }
        Ok(parameters)
    }
    fn encode_generic_arguments_high(
        &self,
        def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> EncodingResult<Vec<vir_high::ty::Type>> {
        assert_eq!(substs.len(), self.env().identity_substs(def_id).len());
        Ok(substs
            .iter()
            // TODO(tymap): ignoring const params and lifetimes for now
            .filter_map(|generic| match generic.unpack() {
                ty::subst::GenericArgKind::Type(ty) => Some(ty),
                _ => None,
            })
            .map(|ty| self.encode_type_high(ty))
            .collect::<Result<Vec<_>, _>>()?)
    }
    fn encode_param(&self, name: Symbol, index: u32) -> vir_high::ty::TypeVar {
        let sanitized_name = name
            .as_str()
            .replace(' ', "_")
            .replace('>', "_gt_")
            .replace('<', "_lt_")
            .replace('=', "_eq_");
        let identifier = format!("{}${}", sanitized_name, index);
        vir_high::ty::TypeVar::generic_type(identifier)
    }
}
