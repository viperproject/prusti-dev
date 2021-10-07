use prusti_common::{config, report::log};
use rustc_middle::ty;
use std::{cell::RefCell, collections::HashMap};
use vir_crate::polymorphic as vir;

use crate::encoder::{
    encoder::SubstMap,
    errors::{EncodingError, EncodingResult},
    utils::transpose,
};

use super::TypeEncoder;

#[derive(Default)]
pub(crate) struct TypeEncoderState<'tcx> {
    fields: RefCell<HashMap<String, vir::Field>>,
    type_predicate_types: RefCell<HashMap<ty::TyKind<'tcx>, vir::Type>>,
    predicate_types: RefCell<HashMap<vir::Type, ty::Ty<'tcx>>>,
    type_predicates: RefCell<HashMap<String, vir::Predicate>>,
    type_invariant_names: RefCell<HashMap<ty::TyKind<'tcx>, String>>,
    type_tag_names: RefCell<HashMap<ty::TyKind<'tcx>, String>>,
    type_invariants: RefCell<HashMap<String, vir::FunctionIdentifier>>,
    type_tags: RefCell<HashMap<String, vir::FunctionIdentifier>>,
}

pub(crate) trait TypeEncoderInterface<'tcx> {
    fn encode_value_field(&self, ty: ty::Ty<'tcx>) -> EncodingResult<vir::Field>;
    fn encode_raw_ref_field(
        &self,
        viper_field_name: String,
        ty: ty::Ty<'tcx>,
    ) -> EncodingResult<vir::Field>;
    fn encode_enum_variant_field(&self, index: &str) -> vir::Field;
    fn encode_discriminant_field(&self) -> vir::Field;
    fn encode_type(&self, ty: ty::Ty<'tcx>) -> EncodingResult<vir::Type>;
    fn encode_type_bounds(&self, var: &vir::Expr, ty: ty::Ty<'tcx>) -> Vec<vir::Expr>;
    fn decode_type_predicate_type(&self, typ: &vir::Type) -> EncodingResult<ty::Ty<'tcx>>;
    fn encode_type_predicate_def(&self, ty: ty::Ty<'tcx>) -> EncodingResult<vir::Predicate>;
    fn encode_type_invariant_use(&self, ty: ty::Ty<'tcx>) -> EncodingResult<String>;
    fn encode_type_invariant_def(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> EncodingResult<vir::FunctionIdentifier>;
    fn encode_type_tag_use(&self, ty: ty::Ty<'tcx>) -> String;
    fn encode_type_tag_def(&self, ty: ty::Ty<'tcx>);
    fn get_used_viper_predicates_map(&self) -> HashMap<String, vir::Predicate>;
    fn get_viper_predicate(&self, name: &str) -> vir::Predicate;
    fn type_substitution_polymorphic_type_map(
        &self,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<HashMap<vir::TypeVar, vir::Type>>;
}

impl<'v, 'tcx: 'v> TypeEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn encode_value_field(&self, ty: ty::Ty<'tcx>) -> EncodingResult<vir::Field> {
        let type_encoder = TypeEncoder::new(self, ty);
        let field = type_encoder.encode_value_field()?;
        self.type_encoder_state
            .fields
            .borrow_mut()
            .entry(field.name.clone())
            .or_insert_with(|| field.clone());
        Ok(field)
    }
    fn encode_raw_ref_field(
        &self,
        viper_field_name: String,
        ty: ty::Ty<'tcx>,
    ) -> EncodingResult<vir::Field> {
        let typ = self.encode_type(ty)?;
        self.type_encoder_state
            .fields
            .borrow_mut()
            .entry(viper_field_name.clone())
            .or_insert_with(|| {
                // Do not store the name of the type in self.fields
                vir::Field::new(viper_field_name.clone(), vir::Type::typed_ref(""))
            });
        Ok(vir::Field::new(viper_field_name, typ))
    }
    /// Creates a field that corresponds to the enum variant ``index``.
    fn encode_enum_variant_field(&self, index: &str) -> vir::Field {
        let name = format!("enum_{}", index);
        let mut fields = self.type_encoder_state.fields.borrow_mut();
        if !fields.contains_key(&name) {
            let field = vir::Field::new(name.clone(), vir::Type::typed_ref(""));
            fields.insert(name.clone(), field);
        }
        fields.get(&name).cloned().unwrap()
    }
    fn encode_discriminant_field(&self) -> vir::Field {
        let name = "discriminant";
        let field = vir::Field::new(name, vir::Type::Int);
        self.type_encoder_state
            .fields
            .borrow_mut()
            .entry(name.to_string())
            .or_insert_with(|| field.clone());
        field
    }
    fn encode_type(&self, ty: ty::Ty<'tcx>) -> EncodingResult<vir::Type> {
        if !self
            .type_encoder_state
            .type_predicate_types
            .borrow()
            .contains_key(ty.kind())
        {
            let type_encoder = TypeEncoder::new(self, ty);
            let encoded_type = type_encoder.encode_type()?;
            self.type_encoder_state
                .type_predicate_types
                .borrow_mut()
                .insert(ty.kind().clone(), encoded_type.clone());
            self.type_encoder_state
                .predicate_types
                .borrow_mut()
                .insert(encoded_type, ty);
            // Trigger encoding of definition
            self.encode_type_predicate_def(ty)?;
        }
        let predicate_type =
            self.type_encoder_state.type_predicate_types.borrow()[ty.kind()].clone();
        Ok(predicate_type)
    }
    fn encode_type_bounds(&self, var: &vir::Expr, ty: ty::Ty<'tcx>) -> Vec<vir::Expr> {
        let type_encoder = TypeEncoder::new(self, ty);
        type_encoder.encode_bounds(var)
    }
    fn decode_type_predicate_type(&self, typ: &vir::Type) -> EncodingResult<ty::Ty<'tcx>> {
        let check = |typ: &vir::Type| {
            if let Some(ty) = self.type_encoder_state.predicate_types.borrow().get(typ) {
                Ok(*ty)
            } else {
                Err(EncodingError::internal(format!(
                    "type predicate not known: {:?}",
                    typ.name()
                )))
            }
        };
        match typ {
            vir::Type::TypeVar(_) | vir::Type::TypedRef(_) => check(typ),
            vir::Type::Snapshot(snapshot) => check(&vir::Type::TypedRef(snapshot.clone().into())),
            _ => Err(EncodingError::internal(format!(
                "type predicate not known: {:?}",
                typ.name()
            ))),
        }
    }
    fn encode_type_predicate_def(&self, ty: ty::Ty<'tcx>) -> EncodingResult<vir::Predicate> {
        let predicate_name = self.encode_type_predicate_use(ty)?;
        if !self
            .type_encoder_state
            .type_predicates
            .borrow()
            .contains_key(&predicate_name)
        {
            let type_encoder = TypeEncoder::new(self, ty);
            let predicates = type_encoder.encode_predicate_def()?;
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
                self.type_encoder_state
                    .type_predicates
                    .borrow_mut()
                    .insert(predicate_name.to_string(), predicate);
            }
        }
        Ok(self.type_encoder_state.type_predicates.borrow()[&predicate_name].clone())
    }

    fn encode_type_invariant_use(&self, ty: ty::Ty<'tcx>) -> EncodingResult<String> {
        // TODO we could use type_predicate_names instead (see TypeEncoder::encode_invariant_use)
        if !self
            .type_encoder_state
            .type_invariant_names
            .borrow()
            .contains_key(ty.kind())
        {
            let type_encoder = TypeEncoder::new(self, ty);
            let invariant_name = type_encoder
                .encode_invariant_use()
                .expect("failed to encode unsupported type");
            self.type_encoder_state
                .type_invariant_names
                .borrow_mut()
                .insert(ty.kind().clone(), invariant_name);
            // Trigger encoding of definition
            self.encode_type_invariant_def(ty)?;
        }
        let invariant_name =
            self.type_encoder_state.type_invariant_names.borrow()[ty.kind()].clone();
        Ok(invariant_name)
    }

    fn encode_type_invariant_def(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> EncodingResult<vir::FunctionIdentifier> {
        let invariant_name = self.encode_type_invariant_use(ty)?;
        if !self
            .type_encoder_state
            .type_invariants
            .borrow()
            .contains_key(&invariant_name)
        {
            let type_encoder = TypeEncoder::new(self, ty);
            let invariant = type_encoder.encode_invariant_def()?;
            let identifier = self.insert_function(invariant);
            self.type_encoder_state
                .type_invariants
                .borrow_mut()
                .insert(invariant_name.clone(), identifier);
        }
        Ok(self.type_encoder_state.type_invariants.borrow()[&invariant_name].clone())
    }

    fn encode_type_tag_use(&self, ty: ty::Ty<'tcx>) -> String {
        if !self
            .type_encoder_state
            .type_tag_names
            .borrow()
            .contains_key(ty.kind())
        {
            let type_encoder = TypeEncoder::new(self, ty);
            let tag_name = type_encoder
                .encode_tag_use()
                .expect("failed to encode unsupported type");
            self.type_encoder_state
                .type_tag_names
                .borrow_mut()
                .insert(ty.kind().clone(), tag_name);
            // Trigger encoding of definition
            self.encode_type_tag_def(ty);
        }
        let tag_name = self.type_encoder_state.type_tag_names.borrow()[ty.kind()].clone();
        tag_name
    }

    fn encode_type_tag_def(&self, ty: ty::Ty<'tcx>) {
        let tag_name = self.encode_type_tag_use(ty);
        if !self
            .type_encoder_state
            .type_tags
            .borrow()
            .contains_key(&tag_name)
        {
            let type_encoder = TypeEncoder::new(self, ty);
            let tag = type_encoder.encode_tag_def();
            let identifier = self.insert_function(tag);
            self.type_encoder_state
                .type_tags
                .borrow_mut()
                .insert(tag_name, identifier);
        }
    }
    fn get_used_viper_predicates_map(&self) -> HashMap<String, vir::Predicate> {
        self.type_encoder_state.type_predicates.borrow().clone()
    }

    fn get_viper_predicate(&self, name: &str) -> vir::Predicate {
        self.type_encoder_state.type_predicates.borrow()[name].clone()
    }
    fn type_substitution_polymorphic_type_map(
        &self,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<HashMap<vir::TypeVar, vir::Type>> {
        tymap
            .iter()
            .map(|(typ, subst)| {
                let typ_encoder = TypeEncoder::new(self, typ);
                let subst_encoder = TypeEncoder::new(self, subst);

                transpose((
                    Ok(typ_encoder.encode_type()?.get_type_var().unwrap()),
                    subst_encoder.encode_type(),
                ))
                // FIXME: unwrap
            })
            .collect::<Result<_, _>>()
    }
}
