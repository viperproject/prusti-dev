use crate::encoder::{
    encoder::SubstMap,
    errors::{EncodingError, EncodingResult},
    high::types::HighTypeEncoderInterface,
    utils::transpose,
};
use prusti_common::{config, report::log};
use rustc_middle::ty;
use std::{cell::RefCell, collections::HashMap};
use vir_crate::{high as vir_high, polymorphic as vir};

use super::TypeEncoder;

#[derive(Default)]
pub(crate) struct MirTypeEncoderState<'tcx> {
    type_predicate_types: RefCell<HashMap<ty::TyKind<'tcx>, vir::Type>>,
    predicate_types: RefCell<HashMap<vir::Type, ty::Ty<'tcx>>>,
    type_predicates: RefCell<HashMap<String, vir::Predicate>>,
    type_invariant_names: RefCell<HashMap<ty::TyKind<'tcx>, String>>,
    type_tag_names: RefCell<HashMap<ty::TyKind<'tcx>, String>>,
    type_invariants: RefCell<HashMap<String, vir::FunctionIdentifier>>,
    type_tags: RefCell<HashMap<String, vir::FunctionIdentifier>>,

    /// A mapping from `vir_high` types to information needed for encoding them.
    type_descriptions: RefCell<HashMap<vir_high::Type, TypeDescription<'tcx>>>,
}

/// All necessary information for encoding a `vir::high` type.
struct TypeDescription<'tcx> {
    /// Original MIR type.
    mir_type: ty::Ty<'tcx>,
}

pub(crate) trait MirTypeEncoderInterface<'tcx> {
    fn encode_value_field(&self, ty: ty::Ty<'tcx>) -> EncodingResult<vir::Field>;
    fn encode_raw_ref_field(
        &self,
        viper_field_name: String,
        ty: ty::Ty<'tcx>,
    ) -> EncodingResult<vir::Field>;
    fn encode_enum_variant_field(&self, index: &str) -> vir::Field;
    fn encode_discriminant_field(&self) -> vir::Field;
    // TODO: Change the type to vir_high.
    fn encode_type_high(&self, ty: ty::Ty<'tcx>) -> EncodingResult<vir::Type>;
    fn encode_type_bounds(&self, var: &vir::Expr, ty: ty::Ty<'tcx>) -> Vec<vir::Expr>;
    fn decode_type_predicate_type(&self, typ: &vir::Type) -> EncodingResult<ty::Ty<'tcx>>;
    fn encode_type_def(&self, ty: ty::Ty<'tcx>) -> EncodingResult<Vec<vir::Predicate>>;
    fn encode_type_invariant_use(&self, ty: ty::Ty<'tcx>) -> EncodingResult<String>;
    fn encode_type_invariant_def(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> EncodingResult<vir::FunctionIdentifier>;
    fn encode_type_tag_use(&self, ty: ty::Ty<'tcx>) -> String;
    fn encode_type_tag_def(&self, ty: ty::Ty<'tcx>);
    fn type_substitution_polymorphic_type_map(
        &self,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<HashMap<vir::TypeVar, vir::Type>>;
}

impl<'v, 'tcx: 'v> MirTypeEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn encode_value_field(&self, ty: ty::Ty<'tcx>) -> EncodingResult<vir::Field> {
        let type_encoder = TypeEncoder::new(self, ty);
        let field = type_encoder.encode_value_field()?;
        Ok(field)
    }
    fn encode_raw_ref_field(
        &self,
        viper_field_name: String,
        ty: ty::Ty<'tcx>,
    ) -> EncodingResult<vir::Field> {
        let typ = self.encode_type(ty)?;
        Ok(vir::Field::new(viper_field_name, typ))
    }
    /// Creates a field that corresponds to the enum variant ``index``.
    fn encode_enum_variant_field(&self, index: &str) -> vir::Field {
        let name = format!("enum_{}", index);
        vir::Field::new(name.clone(), vir::Type::typed_ref(""))
    }
    fn encode_discriminant_field(&self) -> vir::Field {
        let name = "discriminant";
        let field = vir::Field::new(name, vir::Type::Int);
        field
    }
    fn encode_type_high(&self, ty: ty::Ty<'tcx>) -> EncodingResult<vir::Type> {
        if !self
            .mir_type_encoder_state
            .type_predicate_types
            .borrow()
            .contains_key(ty.kind())
        {
            let type_encoder = TypeEncoder::new(self, ty);
            let encoded_type = type_encoder.encode_type()?;
            self.mir_type_encoder_state
                .type_predicate_types
                .borrow_mut()
                .insert(ty.kind().clone(), encoded_type.clone());
            self.mir_type_encoder_state
                .predicate_types
                .borrow_mut()
                .insert(encoded_type, ty);
        }
        let predicate_type =
            self.mir_type_encoder_state.type_predicate_types.borrow()[ty.kind()].clone();
        Ok(predicate_type)
    }
    fn encode_type_bounds(&self, var: &vir::Expr, ty: ty::Ty<'tcx>) -> Vec<vir::Expr> {
        let type_encoder = TypeEncoder::new(self, ty);
        type_encoder.encode_bounds(var)
    }
    fn decode_type_predicate_type(&self, typ: &vir::Type) -> EncodingResult<ty::Ty<'tcx>> {
        let check = |typ: &vir::Type| {
            if let Some(ty) = self
                .mir_type_encoder_state
                .predicate_types
                .borrow()
                .get(typ)
            {
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
    // TODO: Change the return type to vir_high::TypeDef
    fn encode_type_def(&self, ty: ty::Ty<'tcx>) -> EncodingResult<Vec<vir::Predicate>> {
        let type_encoder = TypeEncoder::new(self, ty);
        let predicates = type_encoder.encode_predicate_def()?;
        Ok(predicates)
    }
    fn encode_type_invariant_use(&self, ty: ty::Ty<'tcx>) -> EncodingResult<String> {
        // TODO we could use type_predicate_names instead (see TypeEncoder::encode_invariant_use)
        if !self
            .mir_type_encoder_state
            .type_invariant_names
            .borrow()
            .contains_key(ty.kind())
        {
            let type_encoder = TypeEncoder::new(self, ty);
            let invariant_name = type_encoder
                .encode_invariant_use()
                .expect("failed to encode unsupported type");
            self.mir_type_encoder_state
                .type_invariant_names
                .borrow_mut()
                .insert(ty.kind().clone(), invariant_name);
            // Trigger encoding of definition
            self.encode_type_invariant_def(ty)?;
        }
        let invariant_name =
            self.mir_type_encoder_state.type_invariant_names.borrow()[ty.kind()].clone();
        Ok(invariant_name)
    }
    fn encode_type_invariant_def(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> EncodingResult<vir::FunctionIdentifier> {
        let invariant_name = self.encode_type_invariant_use(ty)?;
        if !self
            .mir_type_encoder_state
            .type_invariants
            .borrow()
            .contains_key(&invariant_name)
        {
            let type_encoder = TypeEncoder::new(self, ty);
            let invariant = type_encoder.encode_invariant_def()?;
            let identifier = self.insert_function(invariant);
            self.mir_type_encoder_state
                .type_invariants
                .borrow_mut()
                .insert(invariant_name.clone(), identifier);
        }
        Ok(self.mir_type_encoder_state.type_invariants.borrow()[&invariant_name].clone())
    }
    fn encode_type_tag_use(&self, ty: ty::Ty<'tcx>) -> String {
        if !self
            .mir_type_encoder_state
            .type_tag_names
            .borrow()
            .contains_key(ty.kind())
        {
            let type_encoder = TypeEncoder::new(self, ty);
            let tag_name = type_encoder
                .encode_tag_use()
                .expect("failed to encode unsupported type");
            self.mir_type_encoder_state
                .type_tag_names
                .borrow_mut()
                .insert(ty.kind().clone(), tag_name);
            // Trigger encoding of definition
            self.encode_type_tag_def(ty);
        }
        let tag_name = self.mir_type_encoder_state.type_tag_names.borrow()[ty.kind()].clone();
        tag_name
    }
    fn encode_type_tag_def(&self, ty: ty::Ty<'tcx>) {
        let tag_name = self.encode_type_tag_use(ty);
        if !self
            .mir_type_encoder_state
            .type_tags
            .borrow()
            .contains_key(&tag_name)
        {
            let type_encoder = TypeEncoder::new(self, ty);
            let tag = type_encoder.encode_tag_def();
            let identifier = self.insert_function(tag);
            self.mir_type_encoder_state
                .type_tags
                .borrow_mut()
                .insert(tag_name, identifier);
        }
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
