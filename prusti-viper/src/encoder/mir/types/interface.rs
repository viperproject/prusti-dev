use super::TypeEncoder;
use crate::encoder::{
    errors::{EncodingError, EncodingResult, SpannedEncodingResult},
    high::types::HighTypeEncoderInterface,
};

use rustc_errors::MultiSpan;
use rustc_hash::FxHashMap;
use rustc_middle::{mir, ty};
use std::cell::RefCell;
use vir_crate::{common::expression::less_equals, high as vir_high, polymorphic as vir};

#[derive(Default)]
pub(crate) struct MirTypeEncoderState<'tcx> {
    encoded_types: RefCell<FxHashMap<ty::TyKind<'tcx>, vir_high::Type>>,
    encoded_types_inverse: RefCell<FxHashMap<vir_high::Type, ty::Ty<'tcx>>>,
    encoded_type_decls: RefCell<FxHashMap<vir_high::Type, vir_high::TypeDecl>>,
}

pub(crate) trait MirTypeEncoderInterface<'tcx> {
    fn get_type_definition_span(&self, ty: ty::Ty<'tcx>) -> MultiSpan;
    fn get_type_definition_span_high(&self, ty: &vir_high::Type) -> MultiSpan;
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
    fn is_zst(&self, ty: &vir_high::Type) -> SpannedEncodingResult<bool>;
    fn get_integer_type_bounds(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> Option<(vir_high::Expression, vir_high::Expression)>;
    fn encode_type_def(&self, ty: &vir_high::Type) -> SpannedEncodingResult<vir_high::TypeDecl>;
    fn encode_adt_def(
        &self,
        adt_def: ty::AdtDef<'tcx>,
        substs: ty::subst::SubstsRef<'tcx>,
        variant_index: Option<rustc_target::abi::VariantIdx>,
    ) -> SpannedEncodingResult<vir_high::TypeDecl>;
    fn encode_type_bounds_high(
        &self,
        var: &vir_high::Expression,
        ty: ty::Ty<'tcx>,
    ) -> Vec<vir_high::Expression>;
}

impl<'v, 'tcx: 'v> MirTypeEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn get_type_definition_span(&self, ty: ty::Ty<'tcx>) -> MultiSpan {
        let type_encoder = TypeEncoder::new(self, ty);
        type_encoder.get_definition_span()
    }
    fn get_type_definition_span_high(&self, ty: &vir_high::Type) -> MultiSpan {
        let original_ty = self.decode_type_high(ty);
        self.get_type_definition_span(original_ty)
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
                field.index(),
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
                field.index(),
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
                .insert(encoded_type.clone(), ty);
            let mut encoded_type = encoded_type;
            encoded_type.erase_lifetime();
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
            let variant = &adt_def.variants()[variant_index];
            let name = variant.ident(self.env().tcx()).to_string();
            Ok(name.into())
        } else {
            Err(EncodingError::internal(format!("{:?} is not an enum", ty)))
        }
    }
    fn decode_type_high(&self, ty: &vir_high::Type) -> ty::Ty<'tcx> {
        if let Some(ty_without_variant) = ty.forget_variant() {
            self.mir_type_encoder_state.encoded_types_inverse.borrow()[&ty_without_variant]
        } else if ty == &vir_high::Type::Bool {
            // Bools may be generated by our encoding without having them in the
            // original program.
            self.env().tcx().mk_ty(ty::TyKind::Bool)
        } else if ty == &vir_high::Type::Int(vir_high::ty::Int::Usize) {
            // Usizes may be generated by our encoding without having them in
            // the original program.
            self.env().tcx().mk_ty(ty::TyKind::Uint(ty::UintTy::Usize))
        } else if let vir_high::Type::Pointer(pointer) = ty {
            // We use pointer types for modelling addresses of references.
            let target_type = self.decode_type_high(&pointer.target_type);
            self.env().tcx().mk_ty(ty::TyKind::RawPtr(ty::TypeAndMut {
                ty: target_type,
                mutbl: mir::Mutability::Mut,
            }))
        } else if let Some(ty) = self
            .mir_type_encoder_state
            .encoded_types_inverse
            .borrow()
            .get(ty)
        {
            *ty
        } else {
            unreachable!("failed to decode: {}", ty)
        }
    }
    fn is_zst(&self, ty: &vir_high::Type) -> SpannedEncodingResult<bool> {
        let mir_type = self.decode_type_high(ty);
        let param_env = ty::ParamEnv::reveal_all();
        let key = ty::ParamEnvAnd {
            param_env,
            value: mir_type,
        };
        let layout = self.env().tcx().layout_of(key).unwrap();
        Ok(layout.is_zst())
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
            let encoded_type = match ty {
                vir_high::Type::Enum(vir_high::ty::Enum {
                    variant: Some(variant),
                    name,
                    arguments,
                }) => {
                    let encoded_enum = self
                        .encode_type_def(&vir_high::Type::enum_(
                            name.clone(),
                            arguments.clone(),
                            None,
                        ))?
                        .unwrap_enum();
                    vir_high::TypeDecl::Struct(encoded_enum.into_variant(&variant.index).unwrap())
                }
                vir_high::Type::Union(vir_high::ty::Union {
                    variant: Some(variant),
                    name,
                    arguments,
                }) => {
                    let encoded_union = self
                        .encode_type_def(&vir_high::Type::union_(
                            name.clone(),
                            arguments.clone(),
                            None,
                        ))?
                        .unwrap_union();
                    vir_high::TypeDecl::Struct(encoded_union.into_variant(&variant.index).unwrap())
                }
                _ => {
                    let original_ty = self.decode_type_high(ty);
                    let type_encoder = TypeEncoder::new(self, original_ty);
                    type_encoder.encode_type_def()?
                }
            };
            self.mir_type_encoder_state
                .encoded_type_decls
                .borrow_mut()
                .insert(ty.clone(), encoded_type);
        }
        let encoded_type = self.mir_type_encoder_state.encoded_type_decls.borrow()[ty].clone();
        Ok(encoded_type)
    }
    fn encode_adt_def(
        &self,
        adt_def: ty::AdtDef<'tcx>,
        substs: ty::subst::SubstsRef<'tcx>,
        variant_index: Option<rustc_target::abi::VariantIdx>,
    ) -> SpannedEncodingResult<vir_high::TypeDecl> {
        super::encoder::encode_adt_def(self, adt_def, substs, variant_index)
    }
    fn encode_type_bounds_high(
        &self,
        var: &vir_high::Expression,
        ty: ty::Ty<'tcx>,
    ) -> Vec<vir_high::Expression> {
        // FIXME: This should be replaced with the type invariant.
        if let Some((lower_bound, upper_bound)) = self.get_integer_type_bounds(ty) {
            vec![
                less_equals(lower_bound, var.clone()),
                less_equals(var.clone(), upper_bound),
            ]
        } else {
            Vec::new()
        }
    }
}
