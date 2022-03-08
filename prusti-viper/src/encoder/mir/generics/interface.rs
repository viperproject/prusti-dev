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

pub(crate) trait MirGenericsEncoderInterface<'tcx> {/*
    fn update_substitution_map(
        &self,
        tymap: SubstMap<'tcx>,
        function_def_id: DefId,
        substs: ty::subst::SubstsRef<'tcx>,
    ) -> EncodingResult<SubstMap<'tcx>>;
    fn encode_substitution_map_high(
        &self,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<FxHashMap<vir_high::ty::TypeVar, vir_high::Type>>;*/
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

impl<'v, 'tcx: 'v> MirGenericsEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {/*
    fn update_substitution_map(
        &self,
        mut tymap: SubstMap<'tcx>,
        function_def_id: DefId,
        substs: ty::subst::SubstsRef<'tcx>,
    ) -> EncodingResult<SubstMap<'tcx>> {
        let tymap_of_call = SubstMap::build(self.env(), function_def_id, substs);
        tymap.extend(tymap_of_call);
        Ok(tymap)
    }
    fn encode_substitution_map_high(
        &self,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<FxHashMap<vir_high::ty::TypeVar, vir_high::Type>> {
        let mut encoded_tymap = FxHashMap::default();
        for (&ty, &subst) in tymap.iter() {
            if let vir_high::Type::TypeVar(type_var) = self.encode_type_high(ty)? {
                let encoded_substitution = self.encode_type_high(subst)?;
                encoded_tymap.insert(type_var, encoded_substitution);
            } else {
                return Err(EncodingError::internal(format!(
                    "expected type variable, got: {:?}",
                    ty
                )));
            }
        }
        Ok(encoded_tymap)
    }*/
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
        /*
        let generics = self.env().tcx().generics_of(def_id);
        let mut arguments = if let Some(parent) = generics.parent {
            self.encode_generic_arguments_high(parent, tymap)?
        } else {
            Vec::new()
        };
        for generic in &generics.params {
            let name = generic.name;
            let index = generics.param_def_id_to_index[&generic.def_id];
            let type_var = ty::ParamTy { index, name };
            let type_var_type = type_var.to_ty(self.env().tcx());

            let maybe_subst = tymap.resolve(&type_var_type);
            let argument = if let Some(subst) = maybe_subst {
                self.encode_type_high(*subst)?
            } else {
                vir_high::ty::Type::TypeVar(self.encode_param(name, index))
            };
            arguments.push(argument);
        }
        Ok(arguments)
        */
        //rustc_middle::ty::subst::InternalSubsts::try_as_type_list(substs)
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
