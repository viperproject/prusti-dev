use crate::encoder::{
    errors::SpannedEncodingResult, high::types::HighTypeEncoderInterface,
    middle::core_proof::lowerer::Lowerer,
};
use std::borrow::Cow;
use vir_crate::middle::{self as vir_mid};

pub(in super::super) trait TypeDeclWalker {
    type Parameters;
    const IS_EMPTY_PRIMITIVE: bool = false;
    fn before(
        &mut self,
        ty: &vir_mid::Type,
        parameters: &Self::Parameters,
        lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<()> {
        let is_empty = lowerer.encoder.is_type_empty(ty)?;
        match ty {
            vir_mid::Type::Bool
            | vir_mid::Type::Int(_)
            | vir_mid::Type::Float(_)
            | vir_mid::Type::Reference(_)
            | vir_mid::Type::Pointer(_)
            | vir_mid::Type::Sequence(_)
            | vir_mid::Type::Map(_) => self.before_primitive(ty, parameters, lowerer),
            // vir_mid::Type::TypeVar(TypeVar) => {},
            vir_mid::Type::Tuple(_)
            | vir_mid::Type::Struct(_)
            | vir_mid::Type::Enum(_)
            | vir_mid::Type::Union(_)
                if is_empty && Self::IS_EMPTY_PRIMITIVE =>
            {
                self.before_primitive(ty, parameters, lowerer)
            }
            vir_mid::Type::Tuple(_)
            | vir_mid::Type::Struct(_)
            | vir_mid::Type::Enum(_)
            | vir_mid::Type::Union(_) => self.before_composite(ty, parameters, lowerer),
            // vir_mid::Type::Array(Array) => {},
            // vir_mid::Type::Never => {},
            // vir_mid::Type::Closure(Closure) => {},
            // vir_mid::Type::Unsupported(Unsupported) => {},
            x => unimplemented!("{}", x),
        }
    }
    fn before_primitive(
        &mut self,
        _ty: &vir_mid::Type,
        _parameters: &Self::Parameters,
        _lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
    fn before_composite(
        &mut self,
        _ty: &vir_mid::Type,
        _parameters: &Self::Parameters,
        _lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
    fn walk_primitive_and_empty(
        &mut self,
        _ty: &vir_mid::Type,
        _parameters: &Self::Parameters,
        _lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
    fn walk_primitive(
        &mut self,
        ty: &vir_mid::Type,
        parameters: &Self::Parameters,
        lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<()> {
        self.walk_primitive_and_empty(ty, parameters, lowerer)
    }
    /// This method must call `Self::walk_type`.
    fn walk_field(
        &mut self,
        ty: &vir_mid::Type,
        field: &vir_mid::FieldDecl,
        parameters: &Self::Parameters,
        lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<()>;
    fn walk_fields<'a>(
        &mut self,
        ty: &vir_mid::Type,
        fields: impl Iterator<Item = Cow<'a, vir_mid::FieldDecl>>,
        parameters: &Self::Parameters,
        lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<()> {
        for field in fields {
            self.walk_field(ty, &field, parameters, lowerer)?;
        }
        Ok(())
    }
    fn walk_enum(
        &mut self,
        ty: &vir_mid::Type,
        decl: &vir_mid::type_decl::Enum,
        parameters: &Self::Parameters,
        lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<()> {
        for variant in &decl.variants {
            let variant_ty = ty.clone().variant(variant.name.clone().into());
            if self.need_walk_type(ty, parameters, lowerer)? {
                self.before(ty, parameters, lowerer)?;
                self.walk_variant(&variant_ty, variant, parameters, lowerer)?;
            }
        }
        Ok(())
    }
    fn walk_uion(
        &mut self,
        ty: &vir_mid::Type,
        decl: &vir_mid::type_decl::Union,
        parameters: &Self::Parameters,
        lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<()> {
        for variant in &decl.variants {
            let variant_ty = ty.clone().variant(variant.name.clone().into());
            if self.need_walk_type(ty, parameters, lowerer)? {
                self.before(ty, parameters, lowerer)?;
                self.walk_variant(&variant_ty, variant, parameters, lowerer)?;
            }
        }
        Ok(())
    }
    fn walk_variant(
        &mut self,
        ty: &vir_mid::Type,
        variant: &vir_mid::type_decl::Struct,
        parameters: &Self::Parameters,
        lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<()> {
        self.walk_fields(ty, variant.iter_fields(), parameters, lowerer)?;
        Ok(())
    }
    fn need_walk_type(
        &mut self,
        _ty: &vir_mid::Type,
        _parameters: &Self::Parameters,
        _lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<bool> {
        Ok(true)
    }
    fn walk_type(
        &mut self,
        ty: &vir_mid::Type,
        parameters: Self::Parameters,
        lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<()> {
        if self.need_walk_type(ty, &parameters, lowerer)? {
            let type_decl = lowerer.encoder.get_type_decl_mid(ty)?;
            self.walk_type_decl(ty, &type_decl, parameters, lowerer)?;
        }
        Ok(())
    }
    fn walk_type_decl(
        &mut self,
        ty: &vir_mid::Type,
        type_decl: &vir_mid::TypeDecl,
        parameters: Self::Parameters,
        lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<()> {
        self.before(ty, &parameters, lowerer)?;
        let is_empty = lowerer.encoder.is_type_empty(ty)?;
        match type_decl {
            vir_mid::TypeDecl::Bool
            | vir_mid::TypeDecl::Int(_)
            | vir_mid::TypeDecl::Float(_)
            | vir_mid::TypeDecl::Reference(_)
            | vir_mid::TypeDecl::Pointer(_)
            | vir_mid::TypeDecl::Sequence(_)
            | vir_mid::TypeDecl::Map(_) => {
                self.walk_primitive(ty, &parameters, lowerer)?;
            }
            // vir_mid::TypeDecl::Trusted(_) => {}
            // vir_mid::TypeDecl::TypeVar(TypeVar) => {},
            vir_mid::TypeDecl::Tuple(_)
            | vir_mid::TypeDecl::Struct(_)
            | vir_mid::TypeDecl::Enum(_)
            | vir_mid::TypeDecl::Union(_)
                if is_empty && Self::IS_EMPTY_PRIMITIVE =>
            {
                self.walk_primitive(ty, &parameters, lowerer)?;
            }
            vir_mid::TypeDecl::Tuple(tuple_decl) => {
                self.walk_fields(ty, tuple_decl.iter_fields(), &parameters, lowerer)?;
            }
            vir_mid::TypeDecl::Struct(struct_decl) => {
                self.walk_fields(ty, struct_decl.iter_fields(), &parameters, lowerer)?;
            }
            vir_mid::TypeDecl::Enum(decl) => {
                self.walk_enum(ty, decl, &parameters, lowerer)?;
            }
            vir_mid::TypeDecl::Union(decl) => {
                self.walk_uion(ty, decl, &parameters, lowerer)?;
            }
            // vir_mid::TypeDecl::Array(Array) => {},
            // vir_mid::TypeDecl::Never => {},
            // vir_mid::TypeDecl::Closure(Closure) => {},
            // vir_mid::TypeDecl::Unsupported(Unsupported) => {},
            x => unimplemented!("{}", x),
        }
        self.after(ty, parameters, lowerer)?;
        Ok(())
    }
    fn after(
        &mut self,
        ty: &vir_mid::Type,
        parameters: Self::Parameters,
        lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<()> {
        let is_empty = lowerer.encoder.is_type_empty(ty)?;
        match ty {
            vir_mid::Type::Bool
            | vir_mid::Type::Int(_)
            | vir_mid::Type::Float(_)
            | vir_mid::Type::Reference(_)
            | vir_mid::Type::Pointer(_)
            | vir_mid::Type::Sequence(_)
            | vir_mid::Type::Map(_) => self.after_primitive(ty, parameters, lowerer),
            // vir_mid::Type::TypeVar(TypeVar) => {},
            vir_mid::Type::Tuple(_)
            | vir_mid::Type::Trusted(_)
            | vir_mid::Type::Struct(_)
            | vir_mid::Type::Enum(_)
            | vir_mid::Type::Union(_)
                if is_empty && Self::IS_EMPTY_PRIMITIVE =>
            {
                self.after_primitive(ty, parameters, lowerer)
            }
            vir_mid::Type::Tuple(_)
            | vir_mid::Type::Trusted(_)
            | vir_mid::Type::Struct(_)
            | vir_mid::Type::Enum(_)
            | vir_mid::Type::Union(_) => self.after_composite(ty, parameters, lowerer),
            // vir_mid::Type::Array(Array) => {},
            // vir_mid::Type::Never => {},
            // vir_mid::Type::Closure(Closure) => {},
            // vir_mid::Type::Unsupported(Unsupported) => {},
            x => unimplemented!("{} {:?}", x, x),
        }
    }
    fn after_primitive(
        &mut self,
        _ty: &vir_mid::Type,
        _parameters: Self::Parameters,
        _lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
    fn after_composite(
        &mut self,
        _ty: &vir_mid::Type,
        _parameters: Self::Parameters,
        _lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}
