use crate::encoder::{
    encoder::SubstMap,
    errors::{EncodingError, EncodingResult, SpannedEncodingResult, WithSpan},
    high::lower::{predicates::IntoPredicates, IntoPolymorphic},
    mir::types::MirTypeEncoderInterface,
    utils::transpose,
};
#[rustfmt::skip]
use ::log::trace;
use prusti_common::{config, report::log};
use rustc_middle::ty;
use std::{cell::RefCell, collections::HashMap};
use vir_crate::{high as vir_high, polymorphic as vir_poly};

#[derive(Default)]
pub(crate) struct HighTypeEncoderState<'tcx> {
    /// A mapping from Rust MIR types to corresponding `vir::polymorphic`
    /// types.
    ///
    /// Note: this is only for caching.
    encoded_types: RefCell<HashMap<ty::TyKind<'tcx>, vir_poly::Type>>,
    lowered_high_types: RefCell<HashMap<vir_high::Type, vir_poly::Type>>,
    lowered_types_inverse: RefCell<HashMap<vir_poly::Type, vir_high::Type>>,

    // type_invariant_names: RefCell<HashMap<ty::TyKind<'tcx>, String>>,
    type_invariants: RefCell<HashMap<String, vir_poly::FunctionIdentifier>>,
    // viper_predicate_descriptions: RefCell<HashMap<String, ViperPredicateDescription>>,
    viper_predicates: RefCell<HashMap<vir_poly::Type, vir_poly::Predicate>>,
}

// /// All necessary information for encoding a Viper predicate.
// struct ViperPredicateDescription {
//     // /// The corresponding type in `vir::high`.
//     // high_type: vir_high::Type,
//     /// The corresponding type in `vir::polymorphic`.
//     polymorphic_type: vir_poly::Type,
// }

pub(in super::super) trait HighTypeEncoderInterfacePrivate {
    fn ensure_viper_predicate_encoded(&self, name: &vir_poly::Type) -> SpannedEncodingResult<()>;
    fn get_interned_lowered_type(
        &self,
        ty: &vir_high::Type,
        constructor: impl FnOnce() -> vir_poly::Type,
    ) -> vir_poly::Type;
}

impl<'v, 'tcx: 'v> HighTypeEncoderInterfacePrivate for super::super::super::Encoder<'v, 'tcx> {
    fn ensure_viper_predicate_encoded(
        &self,
        predicate_name: &vir_poly::Type,
    ) -> SpannedEncodingResult<()> {
        if !self
            .high_type_encoder_state
            .viper_predicates
            .borrow()
            .contains_key(predicate_name)
        {
            let encoded_type = &self.high_type_encoder_state.lowered_types_inverse.borrow()
                [predicate_name]
                .clone();
            let encoded_type_decl = self.encode_type_def(encoded_type)?;
            // FIXME: Change not to use `with_default_span` here.
            let predicates = encoded_type_decl
                .lower(encoded_type, self)
                .set_span_with(|| self.get_type_definition_span(encoded_type))?;
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
                assert!(self
                    .high_type_encoder_state
                    .viper_predicates
                    .borrow_mut()
                    .insert(predicate.get_type().clone(), predicate)
                    .is_none());
            }
        }
        Ok(())
    }
    fn get_interned_lowered_type(
        &self,
        ty: &vir_high::Type,
        constructor: impl FnOnce() -> vir_poly::Type,
    ) -> vir_poly::Type {
        {
            let _fixme = self.high_type_encoder_state.lowered_high_types.borrow_mut();
        }
        let lowered_high_types = self.high_type_encoder_state.lowered_high_types.borrow();
        if let Some(poly_ty) = lowered_high_types.get(ty) {
            poly_ty.clone()
        } else {
            drop(lowered_high_types);
            let poly_ty = constructor();
            self.high_type_encoder_state
                .lowered_high_types
                .borrow_mut()
                .insert(ty.clone(), poly_ty.clone());
            self.high_type_encoder_state
                .lowered_types_inverse
                .borrow_mut()
                .insert(poly_ty.clone(), ty.clone());
            poly_ty
        }
    }
}

pub(crate) trait HighTypeEncoderInterface<'tcx> {
    fn get_used_viper_predicates_map(
        &self,
    ) -> SpannedEncodingResult<HashMap<vir_poly::Type, vir_poly::Predicate>>;
    fn get_viper_predicate(
        &self,
        name: &vir_poly::Type,
    ) -> SpannedEncodingResult<vir_poly::Predicate>;
    fn encode_type_predicate_def(&self, ty: ty::Ty<'tcx>) -> EncodingResult<vir_poly::Predicate>;
    fn ensure_type_predicate_encoded(&self, ty: ty::Ty<'tcx>) -> EncodingResult<()>;
    fn encode_type(&self, ty: ty::Ty<'tcx>) -> EncodingResult<vir_poly::Type>;
    fn encode_value_field(&self, ty: ty::Ty<'tcx>) -> EncodingResult<vir_poly::Field>;
    fn decode_type_predicate_type(&self, typ: &vir_poly::Type) -> EncodingResult<ty::Ty<'tcx>>;
    fn type_substitution_polymorphic_type_map(
        &self,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<HashMap<vir_poly::TypeVar, vir_poly::Type>>;
    fn encode_type_invariant_use(&self, ty: ty::Ty<'tcx>) -> EncodingResult<String>;
    fn encode_type_invariant_def(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> EncodingResult<vir_poly::FunctionIdentifier>;
    fn encode_type_invariant_def_internal(
        &self,
        ty: ty::Ty<'tcx>,
        invariant_name: &str,
    ) -> EncodingResult<vir_poly::FunctionIdentifier>;
    fn encode_type_bounds(&self, var: &vir_poly::Expr, ty: ty::Ty<'tcx>) -> Vec<vir_poly::Expr>;
}

impl<'v, 'tcx: 'v> HighTypeEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn get_used_viper_predicates_map(
        &self,
    ) -> SpannedEncodingResult<HashMap<vir_poly::Type, vir_poly::Predicate>> {
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
    fn get_viper_predicate(
        &self,
        name: &vir_poly::Type,
    ) -> SpannedEncodingResult<vir_poly::Predicate> {
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
            let polymorphic_type = high_type.lower(self);
            self.high_type_encoder_state
                .encoded_types
                .borrow_mut()
                .insert(ty_kind.clone(), polymorphic_type.clone());
            self.high_type_encoder_state
                .lowered_types_inverse
                .borrow_mut()
                .insert(polymorphic_type, high_type);
            // FIXME: Triggering the encoding of definition should not be
            // needed. Currently we have to do this for
            // `get_used_viper_predicates_map` to work. Once we fix the
            // fold-unfold algorithm to not depend on it, we should remove this.
            self.ensure_type_predicate_encoded(ty)?;
        }
        Ok(self.high_type_encoder_state.encoded_types.borrow()[ty_kind].clone())
    }
    fn encode_value_field(&self, ty: ty::Ty<'tcx>) -> EncodingResult<vir_poly::Field> {
        // FIXME: This should not be needed:
        self.ensure_type_predicate_encoded(ty)?;
        let encoded_type = self.encode_type_high(ty)?;
        let field = super::create_value_field(encoded_type)?.lower(self);
        Ok(field)
    }
    fn encode_type_predicate_def(&self, ty: ty::Ty<'tcx>) -> EncodingResult<vir_poly::Predicate> {
        let predicate_name = self.encode_type(ty)?;
        Ok(self.get_viper_predicate(&predicate_name)?)
    }
    fn ensure_type_predicate_encoded(&self, ty: ty::Ty<'tcx>) -> EncodingResult<()> {
        let predicate_name = self.encode_type(ty)?;
        self.ensure_viper_predicate_encoded(&predicate_name)?;
        Ok(())
    }
    fn decode_type_predicate_type(&self, typ: &vir_poly::Type) -> EncodingResult<ty::Ty<'tcx>> {
        let check = |typ: &vir_poly::Type| {
            if let Some(ty) = self
                .high_type_encoder_state
                .lowered_types_inverse
                .borrow()
                .get(typ)
            {
                let original_ty = self.decode_type_high(ty);
                Ok(original_ty)
            } else {
                Err(EncodingError::internal(format!(
                    "type predicate not known: {:?}",
                    typ.name()
                )))
            }
        };
        match typ {
            vir_poly::Type::TypeVar(_) | vir_poly::Type::TypedRef(_) => check(typ),
            vir_poly::Type::Snapshot(snapshot) => {
                check(&vir_poly::Type::TypedRef(snapshot.clone().into()))
            }
            _ => Err(EncodingError::internal(format!(
                "type predicate not known: {:?}",
                typ.name()
            ))),
        }
    }
    fn type_substitution_polymorphic_type_map(
        &self,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<HashMap<vir_poly::TypeVar, vir_poly::Type>> {
        tymap
            .iter()
            .map(|(typ, subst)| {
                let type_var = self.encode_type(typ)?.get_type_var().unwrap();
                let substitution = self.encode_type(subst);

                transpose((Ok(type_var), substitution))
                // FIXME: unwrap
            })
            .collect::<Result<_, _>>()
    }
    fn encode_type_invariant_use(&self, ty: ty::Ty<'tcx>) -> EncodingResult<String> {
        trace!("encode_type_invariant_use: {:?}", ty.kind());
        let encoded_type = self.encode_type_high(ty)?;
        let invariant_name = format!("{}$inv", encoded_type);
        // Trigger encoding of definition.
        // FIXME: This should not be needed.
        self.encode_type_invariant_def_internal(ty, &invariant_name)?;
        Ok(invariant_name)
    }
    fn encode_type_invariant_def(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> EncodingResult<vir_poly::FunctionIdentifier> {
        trace!("encode_type_invariant_def: {:?}", ty.kind());
        let invariant_name = self.encode_type_invariant_use(ty)?;
        self.encode_type_invariant_def_internal(ty, &invariant_name)
    }
    fn encode_type_invariant_def_internal(
        &self,
        ty: ty::Ty<'tcx>,
        invariant_name: &str,
    ) -> EncodingResult<vir_poly::FunctionIdentifier> {
        trace!("encode_type_invariant_def_internal: {:?}", ty.kind());
        if !self
            .high_type_encoder_state
            .type_invariants
            .borrow()
            .contains_key(invariant_name)
        {
            // FIXME: Type invariants are currently not supported.

            // FIXME: We currently cannot correctly lower functions because it
            // is tricky to ensure that the type is lowered to correct type in
            // polymorphic VIR because sometimes primitive types should be
            // lowered to `TypedRef`, sometimes to primitive types.
            let encoded_type = self.encode_type(ty)?;
            let self_local_var = vir_poly::LocalVar::new("self", encoded_type);
            let invariant = vir_poly::Function {
                name: invariant_name.to_string(),
                formal_args: vec![self_local_var],
                return_type: vir_poly::Type::Bool,
                pres: Vec::new(),
                posts: Vec::new(),
                body: Some(true.into()),
            };
            let identifier = self.insert_function(invariant);
            self.high_type_encoder_state
                .type_invariants
                .borrow_mut()
                .insert(invariant_name.to_string(), identifier);
        }
        Ok(self.high_type_encoder_state.type_invariants.borrow()[invariant_name].clone())
    }
    fn encode_type_bounds(&self, var: &vir_poly::Expr, ty: ty::Ty<'tcx>) -> Vec<vir_poly::Expr> {
        // FIXME: This should replaced with the type invariant.
        if let Some((lower_bound, upper_bound)) = self.get_integer_type_bounds(ty) {
            vec![
                vir_poly::Expr::le_cmp(lower_bound.lower(self), var.clone()),
                vir_poly::Expr::le_cmp(var.clone(), upper_bound.lower(self)),
            ]
        } else {
            Vec::new()
        }
    }
}
