use std::collections::HashMap;

use crate::encoder::{
    encoder::SubstMap,
    errors::{EncodingError, EncodingResult},
    mir::types::MirTypeEncoderInterface,
    utils::transpose,
};
use log::debug;
use rustc_hir::def_id::DefId;
use rustc_middle::{mir, span_bug, ty};
use vir_crate::{
    common::expression::BinaryOperationHelpers,
    high::{self as vir_high, operations::ty::Typed},
};

pub(crate) trait GenericsEncoderInterface<'tcx> {
    fn update_substitution_map(
        &self,
        tymap: SubstMap<'tcx>,
        function_def_id: DefId,
        substs: ty::subst::SubstsRef<'tcx>,
    ) -> EncodingResult<SubstMap<'tcx>>;
    fn encode_substitution_map_high(
        &self,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<HashMap<vir_high::ty::TypeVar, vir_high::Type>>;
}

impl<'v, 'tcx: 'v> GenericsEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn update_substitution_map(
        &self,
        mut tymap: SubstMap<'tcx>,
        function_def_id: DefId,
        substs: ty::subst::SubstsRef<'tcx>,
    ) -> EncodingResult<SubstMap<'tcx>> {
        let own_substs = ty::List::identity_for_item(self.env().tcx(), function_def_id);
        for (kind1, kind2) in own_substs.iter().zip(substs.iter()) {
            if let (ty::subst::GenericArgKind::Type(ty), ty::subst::GenericArgKind::Type(subst)) =
                (kind1.unpack(), kind2.unpack())
            {
                for old_subst in tymap.values_mut() {
                    if *old_subst == ty {
                        *old_subst = subst;
                    }
                }
                tymap.insert(ty, subst);
            }
        }
        Ok(tymap)
    }
    fn encode_substitution_map_high(
        &self,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<HashMap<vir_high::ty::TypeVar, vir_high::Type>> {
        let mut encoded_tymap = HashMap::new();
        for (ty, subst) in tymap {
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
    }
}
