use crate::encoder::{
    errors::{EncodingResult, SpannedEncodingResult},
    mir::types::MirTypeEncoderInterface,
};
use prusti_common::{config, report::log};
use rustc_middle::ty;
use std::{cell::RefCell, collections::HashMap};
use vir_crate::{high as vir_high, polymorphic as vir_poly};

#[derive(Default)]
pub(crate) struct HighTypeEncoderState<'tcx> {
    /// A mapping from Rust MIR types to corresponding `vir::polymorphic`
    /// predicates.
    ///
    /// Note: this is only for caching.
    type_predicates: RefCell<HashMap<ty::TyKind<'tcx>, String>>,
    /// A mapping from Rust MIR types to corresponding `vir::polymorphic`
    /// types.
    ///
    /// Note: this is only for caching.
    encoded_types: RefCell<HashMap<ty::TyKind<'tcx>, vir_poly::Type>>,
    /// A mapping from predicate names to information needed for encoding them.
    viper_predicate_descriptions: RefCell<HashMap<String, ViperPredicateDescription>>,
    viper_predicates: RefCell<HashMap<String, vir_poly::Predicate>>,
}

/// All necessary information for encoding a Viper predicate.
struct ViperPredicateDescription {
    // /// The corresponding type in `vir::high`.
    // high_type: vir_high::Type,
    /// The corresponding type in `vir::polymorphic`.
    polymorphic_type: vir_poly::Type,
}

trait Private {
    fn ensure_viper_predicate_encoded(&self, name: &str) -> SpannedEncodingResult<()>;
}

impl<'v, 'tcx: 'v> Private for super::super::super::Encoder<'v, 'tcx> {
    fn ensure_viper_predicate_encoded(&self, name: &str) -> SpannedEncodingResult<()> {
        if !self
            .high_type_encoder_state
            .viper_predicates
            .borrow()
            .contains_key(name)
        {
            unimplemented!();
        }
        Ok(())
    }
}

pub(crate) trait HighTypeEncoderInterface<'tcx> {
    fn get_used_viper_predicates_map(
        &self,
    ) -> SpannedEncodingResult<HashMap<String, vir_poly::Predicate>>;
    fn get_viper_predicate(&self, name: &str) -> SpannedEncodingResult<vir_poly::Predicate>;
    fn encode_type_predicate_use(&self, ty: ty::Ty<'tcx>) -> EncodingResult<String>;
    fn encode_type_predicate_def(&self, ty: ty::Ty<'tcx>) -> EncodingResult<vir_poly::Predicate>;
    fn ensure_type_predicate_encoded(&self, ty: ty::Ty<'tcx>) -> EncodingResult<()>;
    fn encode_type(&self, ty: ty::Ty<'tcx>) -> EncodingResult<vir_poly::Type>;
}

impl<'v, 'tcx: 'v> HighTypeEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn get_used_viper_predicates_map(
        &self,
    ) -> SpannedEncodingResult<HashMap<String, vir_poly::Predicate>> {
        // let predicate_names = self.high_type_encoder_state.viper_predicate_descriptions.borrow().keys().map(|key: &String| key.to_owned()).collect::<Vec<String>>();
        // let mut predicates = HashMap::new();
        // for predicate_name in predicate_names {
        //     let predicate = self.get_viper_predicate(&predicate_name)?;
        //     predicates.insert(predicate_name, predicate);
        // }
        let predicates = self
            .high_type_encoder_state
            .viper_predicates
            .borrow()
            .clone();
        Ok(predicates)
    }
    fn get_viper_predicate(&self, name: &str) -> SpannedEncodingResult<vir_poly::Predicate> {
        self.ensure_viper_predicate_encoded(name)?;
        Ok(self.high_type_encoder_state.viper_predicates.borrow()[name].clone())
    }
    fn encode_type(&self, ty: ty::Ty<'tcx>) -> EncodingResult<vir_poly::Type> {
        let ty_kind = ty.kind();
        if !self
            .high_type_encoder_state
            .encoded_types
            .borrow()
            .contains_key(ty_kind)
        {
            let high_type = self.encode_type_high(ty)?;
            let polymorphic_type = high_type; //.into();
            self.high_type_encoder_state
                .encoded_types
                .borrow_mut()
                .insert(ty_kind.clone(), polymorphic_type);
            // FIXME: Triggering the encoding of definition should not be
            // needed. Currently we have to do this for
            // `get_used_viper_predicates_map` to work. Once we fix the
            // fold-unfold algorithm to not depend on it, we should remove this.
            self.ensure_type_predicate_encoded(ty)?;
        }
        Ok(self.high_type_encoder_state.encoded_types.borrow()[ty_kind].clone())
    }
    fn encode_type_predicate_use(&self, ty: ty::Ty<'tcx>) -> EncodingResult<String> {
        let ty_kind = ty.kind();
        if !self
            .high_type_encoder_state
            .type_predicates
            .borrow()
            .contains_key(ty_kind)
        {
            let mut type_predicates = self.high_type_encoder_state.type_predicates.borrow_mut();
            let polymorphic_type = self.encode_type(ty)?;
            let name = polymorphic_type.encode_as_string();
            type_predicates.insert(ty_kind.clone(), name.clone());
            self.high_type_encoder_state
                .viper_predicate_descriptions
                .borrow_mut()
                .insert(name, ViperPredicateDescription { polymorphic_type });
        }
        Ok(self.high_type_encoder_state.type_predicates.borrow()[ty_kind].clone())
    }
    fn encode_type_predicate_def(&self, ty: ty::Ty<'tcx>) -> EncodingResult<vir_poly::Predicate> {
        let predicate_name = self.encode_type_predicate_use(ty)?;
        Ok(self.get_viper_predicate(&predicate_name)?)
    }
    fn ensure_type_predicate_encoded(&self, ty: ty::Ty<'tcx>) -> EncodingResult<()> {
        let predicate_name = self.encode_type_predicate_use(ty)?;
        if !self
            .high_type_encoder_state
            .viper_predicates
            .borrow()
            .contains_key(&predicate_name)
        {
            // let type_def = self.encode_type_def(ty)?;
            // TODO: Convert into vir::poly::Predicates.
            let predicates = self.encode_type_def(ty)?;
            for predicate in predicates {
                self.log_vir_program_before_viper(predicate.to_string());
                let predicate_name = predicate.name();
                if config::dump_debug_info() {
                    log::report(
                        "vir_predicates",
                        format!("{}.vir", predicate_name),
                        predicate.to_string(),
                    );
                }
                self.high_type_encoder_state
                    .viper_predicates
                    .borrow_mut()
                    .insert(predicate_name.to_string(), predicate);
            }
        }
        Ok(())
    }
}
