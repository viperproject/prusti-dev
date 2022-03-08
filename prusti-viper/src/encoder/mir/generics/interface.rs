use crate::encoder::{
    errors::{EncodingError, EncodingResult},
    mir::types::MirTypeEncoderInterface,
};

use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty;
use rustc_middle::ty::subst::SubstsRef;
use rustc_span::symbol::Symbol;
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
        // FIXME: why can try_as_type_list not be called here?
        //rustc_middle::ty::subst::InternalSubsts::try_as_type_list(substs)

        // assumption: the `substs` passed to this method is a correct `substs`
        // for the given `DefId`
        // FIXME: debug_assert some check for this (e.g. that `identity_for_item`
        // has the same length as `substs`)
        Ok(substs
            .iter()
            .map(|subst| subst.expect_ty())
            .map(|subst| self.encode_type_high(subst))
            .collect::<Result<Vec<_>, _>>()?)
    }
    fn encode_param(&self, name: Symbol, index: u32) -> vir_high::ty::TypeVar {
        let identifier = format!("{}${}", name.as_str(), index);
        vir_high::ty::TypeVar::generic_type(identifier)
    }
}
