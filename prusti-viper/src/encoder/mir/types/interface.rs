use super::TypeEncoder;
use crate::encoder::{
    encoder::SubstMap,
    errors::{EncodingError, EncodingResult, SpannedEncodingResult},
    high::types::HighTypeEncoderInterface,
    utils::transpose,
};
use rustc_hir::def_id::DefId;
#[rustfmt::skip]
use ::log::trace;
use prusti_common::{config, report::log};
use rustc_middle::{mir, ty};
use rustc_span::MultiSpan;
use std::{cell::RefCell, collections::HashMap};
use vir_crate::{common::expression::less_equals, high as vir_high, polymorphic as vir};

#[derive(Default)]
pub(crate) struct MirTypeEncoderState<'tcx> {
    encoded_types: RefCell<HashMap<ty::TyKind<'tcx>, vir_high::Type>>,
    encoded_types_inverse: RefCell<HashMap<vir_high::Type, ty::Ty<'tcx>>>,
    encoded_type_decls: RefCell<HashMap<vir_high::Type, vir_high::TypeDecl>>,

    type_tag_names: RefCell<HashMap<ty::TyKind<'tcx>, String>>,
    type_tags: RefCell<HashMap<String, vir::FunctionIdentifier>>,
}

pub(crate) trait MirTypeEncoderInterface<'tcx> {
    fn get_type_definition_span(&self, ty: &vir_high::Type) -> MultiSpan;
    // fn encode_value_field_high(&self, ty: ty::Ty<'tcx>) -> EncodingResult<vir_high::FieldDecl>;
    fn encode_raw_ref_field(
        &self,
        viper_field_name: String,
        ty: ty::Ty<'tcx>,
    ) -> EncodingResult<vir::Field>;
    fn encode_enum_variant_field(&self, index: &str) -> vir::Field;
    fn encode_discriminant_field(&self) -> vir::Field;
    fn encode_field(
        &self,
        ty: &vir_high::Type,
        index: mir::Field,
    ) -> EncodingResult<vir_high::FieldDecl>;
    fn encode_value_field_high(&self, ty: ty::Ty<'tcx>) -> EncodingResult<vir_high::FieldDecl>;
    fn encode_type_high(&self, ty: ty::Ty<'tcx>) -> SpannedEncodingResult<vir_high::Type>;
    fn encode_place_type_high(&self, ty: mir::tcx::PlaceTy<'tcx>)
        -> EncodingResult<vir_high::Type>;
    fn encode_enum_variant_index_high(
        &self,
        ty: ty::Ty<'tcx>,
        variant: rustc_target::abi::VariantIdx,
    ) -> EncodingResult<vir_high::ty::VariantIndex>;
    fn decode_type_high(&self, ty: &vir_high::Type) -> ty::Ty<'tcx>;
    fn get_integer_type_bounds(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> Option<(vir_high::Expression, vir_high::Expression)>;
    fn encode_type_def(&self, ty: &vir_high::Type) -> SpannedEncodingResult<vir_high::TypeDecl>;
    fn encode_type_invariant_def_high(
        &self,
        ty: ty::Ty<'tcx>,
        invariant_name: &str,
    ) -> EncodingResult<vir_high::FunctionDecl>;
    fn encode_type_tag_use(&self, ty: ty::Ty<'tcx>) -> String;
    fn encode_type_tag_def(&self, ty: ty::Ty<'tcx>);
}

impl<'v, 'tcx: 'v> MirTypeEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn get_type_definition_span(&self, ty: &vir_high::Type) -> MultiSpan {
        let original_ty = self.decode_type_high(ty);
        let type_encoder = TypeEncoder::new(self, original_ty);
        type_encoder.get_definition_span()
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
        vir::Field::new(name, vir::Type::typed_ref(""))
    }
    fn encode_discriminant_field(&self) -> vir::Field {
        let name = "discriminant";
        vir::Field::new(name, vir::Type::Int)
    }
    fn encode_field(
        &self,
        ty: &vir_high::Type,
        field: mir::Field,
    ) -> EncodingResult<vir_high::FieldDecl> {
        let type_decl = self.encode_type_def(ty)?;
        let field_decl = match type_decl {
            vir_high::TypeDecl::Tuple(item) => vir_high::FieldDecl::new(
                format!("tuple_{}", field.index()),
                item.arguments[field.index()].clone(),
            ),
            vir_high::TypeDecl::Struct(item) => item.fields[field.index()].clone(),
            vir_high::TypeDecl::Enum(item) => {
                let variant = item
                    .get_variant(ty)
                    .ok_or_else(|| EncodingError::internal("not found variant"))?;
                variant.fields[field.index()].clone()
            }
            vir_high::TypeDecl::Closure(item) => vir_high::FieldDecl::new(
                format!("closure_{}", field.index()),
                item.arguments[field.index()].clone(),
            ),
            _ => {
                return Err(EncodingError::internal(format!(
                    "{} has no fields",
                    type_decl
                )));
            }
        };
        Ok(field_decl)
    }
    fn encode_value_field_high(&self, ty: ty::Ty<'tcx>) -> EncodingResult<vir_high::FieldDecl> {
        // FIXME: This should not be needed:
        self.ensure_type_predicate_encoded(ty)?;
        let encoded_type = self.encode_type_high(ty)?;
        crate::encoder::high::types::create_value_field(encoded_type)
    }
    fn encode_type_high(&self, ty: ty::Ty<'tcx>) -> SpannedEncodingResult<vir_high::Type> {
        if !self
            .mir_type_encoder_state
            .encoded_types
            .borrow()
            .contains_key(ty.kind())
        {
            let type_encoder = TypeEncoder::new(self, ty);
            let encoded_type = type_encoder.encode_type()?;
            assert!(self
                .mir_type_encoder_state
                .encoded_types
                .borrow_mut()
                .insert(ty.kind().clone(), encoded_type.clone())
                .is_none());
            // Note: Multiple ty::Ty<'tcx> types are mapped to the same
            // vir_high::Type type. However, this should not be the problem for
            // using the inverse because we care only between differences that
            // are not dropped in the translation.
            self.mir_type_encoder_state
                .encoded_types_inverse
                .borrow_mut()
                .insert(encoded_type, ty);
        }
        let encoded_type = self.mir_type_encoder_state.encoded_types.borrow()[ty.kind()].clone();
        Ok(encoded_type)
    }
    fn encode_place_type_high(
        &self,
        place_ty: mir::tcx::PlaceTy<'tcx>,
    ) -> EncodingResult<vir_high::Type> {
        let mut encoded_type = self.encode_type_high(place_ty.ty)?;
        if let Some(variant_index) = place_ty.variant_index {
            if let vir_high::Type::Enum(enum_type) = &mut encoded_type {
                assert!(enum_type.variant.is_none());
                enum_type.variant =
                    Some(self.encode_enum_variant_index_high(place_ty.ty, variant_index)?);
            }
        }
        Ok(encoded_type)
    }
    fn encode_enum_variant_index_high(
        &self,
        ty: ty::Ty<'tcx>,
        variant_index: rustc_target::abi::VariantIdx,
    ) -> EncodingResult<vir_high::ty::VariantIndex> {
        if let ty::TyKind::Adt(adt_def, _) = ty.kind() {
            let variant = &adt_def.variants[variant_index];
            let name = variant.ident.to_string();
            Ok(name.into())
        } else {
            Err(EncodingError::internal(format!("{:?} is not an enum", ty)))
        }
    }
    fn decode_type_high(&self, ty: &vir_high::Type) -> ty::Ty<'tcx> {
        if let Some(ty_without_variant) = ty.forget_variant() {
            self.mir_type_encoder_state.encoded_types_inverse.borrow()[&ty_without_variant]
        } else {
            self.mir_type_encoder_state.encoded_types_inverse.borrow()[ty]
        }
    }
    fn get_integer_type_bounds(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> Option<(vir_high::Expression, vir_high::Expression)> {
        let type_encoder = TypeEncoder::new(self, ty);
        // FIXME: This should replaced with the type invariant.
        type_encoder.get_integer_bounds()
    }
    fn encode_type_def(&self, ty: &vir_high::Type) -> SpannedEncodingResult<vir_high::TypeDecl> {
        if !self
            .mir_type_encoder_state
            .encoded_type_decls
            .borrow()
            .contains_key(ty)
        {
            let original_ty = self.decode_type_high(ty);
            let type_encoder = TypeEncoder::new(self, original_ty);
            let encoded_type = type_encoder.encode_type_def()?;
            self.mir_type_encoder_state
                .encoded_type_decls
                .borrow_mut()
                .insert(ty.clone(), encoded_type);
        }
        let encoded_type = self.mir_type_encoder_state.encoded_type_decls.borrow()[ty].clone();
        Ok(encoded_type)
    }
    fn encode_type_invariant_def_high(
        &self,
        ty: ty::Ty<'tcx>,
        invariant_name: &str,
    ) -> EncodingResult<vir_high::FunctionDecl> {
        trace!("encode_type_invariant_def_high: {:?}", ty.kind());
        let type_encoder = TypeEncoder::new(self, ty);
        let invariant = type_encoder.encode_invariant_def(invariant_name)?;
        Ok(invariant)
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
            let _tag = type_encoder.encode_tag_def();
            unimplemented!();
            // let identifier = self.insert_function(tag);
            // self.mir_type_encoder_state
            //     .type_tags
            //     .borrow_mut()
            //     .insert(tag_name, identifier);
        }
    }
}
