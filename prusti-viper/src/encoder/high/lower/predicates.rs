use super::super::types::{create_value_field, interface::HighTypeEncoderInterfacePrivate};
use crate::encoder::{errors::EncodingResult, high::lower::IntoPolymorphic};
use vir_crate::{high as vir_high, polymorphic as vir_poly};
use vir_poly::Predicate;

type Predicates = EncodingResult<Vec<vir_poly::Predicate>>;

pub(in super::super) trait IntoPredicates {
    fn lower(
        &self,
        ty: &vir_high::Type,
        encoder: &impl HighTypeEncoderInterfacePrivate,
    ) -> Predicates;
}

impl IntoPredicates for vir_high::TypeDecl {
    fn lower(
        &self,
        ty: &vir_high::Type,
        encoder: &impl HighTypeEncoderInterfacePrivate,
    ) -> Predicates {
        match self {
            vir_high::TypeDecl::Bool => construct_bool_predicate(encoder),
            vir_high::TypeDecl::Int(ty_decl) => ty_decl.lower(ty, encoder),
            vir_high::TypeDecl::TypeVar(ty_decl) => ty_decl.lower(ty, encoder),
            vir_high::TypeDecl::Tuple(ty_decl) => ty_decl.lower(ty, encoder),
            vir_high::TypeDecl::Struct(ty_decl) => ty_decl.lower(ty, encoder),
            vir_high::TypeDecl::Enum(ty_decl) => ty_decl.lower(ty, encoder),
            vir_high::TypeDecl::Array(ty_decl) => ty_decl.lower(ty, encoder),
            vir_high::TypeDecl::Reference(ty_decl) => ty_decl.lower(ty, encoder),
            vir_high::TypeDecl::Never => construct_never_predicate(encoder),
            vir_high::TypeDecl::Closure(ty_decl) => ty_decl.lower(ty, encoder),
            vir_high::TypeDecl::Unsupported(ty_decl) => ty_decl.lower(ty, encoder),
        }
    }
}

fn construct_bool_predicate(encoder: &impl HighTypeEncoderInterfacePrivate) -> Predicates {
    let ty = vir_high::Type::Bool;
    let field = create_value_field(ty.clone())?.lower(encoder);
    let predicate = Predicate::new_primitive_value(ty.lower(encoder), field, None, None);
    Ok(vec![predicate])
}

impl IntoPredicates for vir_high::type_decl::Int {
    fn lower(
        &self,
        ty: &vir_high::Type,
        encoder: &impl HighTypeEncoderInterfacePrivate,
    ) -> Predicates {
        let field = create_value_field(ty.clone())?.lower(encoder);
        let predicate = Predicate::new_primitive_value(
            ty.lower(encoder),
            field,
            self.lower_bound
                .as_ref()
                .map(|bound| (**bound).lower(encoder)),
            self.upper_bound
                .as_ref()
                .map(|bound| (**bound).lower(encoder)),
        );
        Ok(vec![predicate])
    }
}

impl IntoPredicates for vir_high::type_decl::TypeVar {
    fn lower(
        &self,
        ty: &vir_high::Type,
        encoder: &impl HighTypeEncoderInterfacePrivate,
    ) -> Predicates {
        let predicate = Predicate::new_abstract(ty.lower(encoder));
        Ok(vec![predicate])
    }
}

impl IntoPredicates for vir_high::type_decl::Tuple {
    fn lower(
        &self,
        ty: &vir_high::Type,
        encoder: &impl HighTypeEncoderInterfacePrivate,
    ) -> Predicates {
        let fields = self
            .arguments
            .iter()
            .enumerate()
            .map(|(field_num, ty)| {
                let field_name = format!("tuple_{}", field_num);
                vir_high::FieldDecl::new(field_name, ty.clone()).lower(encoder)
            })
            .collect();
        let predicate = Predicate::new_struct(ty.lower(encoder), fields);
        Ok(vec![predicate])
    }
}

fn lower_struct(
    struct_: &vir_high::type_decl::Struct,
    ty: &vir_high::Type,
    encoder: &impl HighTypeEncoderInterfacePrivate,
) -> EncodingResult<vir_poly::StructPredicate> {
    let fields = struct_
        .fields
        .iter()
        .map(|field| field.lower(encoder))
        .collect();
    Ok(vir_poly::StructPredicate::new(ty.lower(encoder), fields))
}

impl IntoPredicates for vir_high::type_decl::Struct {
    fn lower(
        &self,
        ty: &vir_high::Type,
        encoder: &impl HighTypeEncoderInterfacePrivate,
    ) -> Predicates {
        let predicate = Predicate::Struct(lower_struct(self, ty, encoder)?);
        Ok(vec![predicate])
    }
}

impl IntoPredicates for vir_high::type_decl::Enum {
    fn lower(
        &self,
        ty: &vir_high::Type,
        encoder: &impl HighTypeEncoderInterfacePrivate,
    ) -> Predicates {
        let lower_type = ty.lower(encoder);

        let discriminant_field = vir_high::FieldDecl::discriminant().lower(encoder);
        let this = Predicate::construct_this(lower_type);
        let discriminant_loc = vir_poly::Expr::from(this.clone()).field(discriminant_field.clone());

        let mut variants = Vec::new();
        for (variant, discriminant) in self.variants.iter().zip(self.discriminant_values.clone()) {
            let guard =
                vir_poly::Expr::eq_cmp(discriminant_loc.clone(), discriminant.lower(encoder));
            let variant_ty = ty.clone().variant(variant.name.clone().into());
            let predicate = lower_struct(variant, &variant_ty, encoder)?;
            variants.push((guard, variant.name.clone(), predicate));
        }
        let mut predicates: Vec<_> = variants
            .iter()
            .filter(|(_, _, predicate)| !predicate.has_empty_body())
            .map(|(_, _, predicate)| Predicate::Struct(predicate.clone()))
            .collect();
        let discriminant_bounds = self.discriminant_bounds.lower(encoder).replace_place(
            &vir_high::Expression::discriminant().lower(encoder),
            &discriminant_loc,
        );
        let enum_predicate =
            Predicate::new_enum(this, discriminant_field, discriminant_bounds, variants);
        predicates.push(enum_predicate);
        Ok(predicates)
    }
}

impl IntoPredicates for vir_high::type_decl::Array {
    fn lower(
        &self,
        ty: &vir_high::Type,
        encoder: &impl HighTypeEncoderInterfacePrivate,
    ) -> Predicates {
        let predicate = Predicate::new_abstract(ty.lower(encoder));
        Ok(vec![predicate])
    }
}

impl IntoPredicates for vir_high::type_decl::Reference {
    fn lower(
        &self,
        ty: &vir_high::Type,
        encoder: &impl HighTypeEncoderInterfacePrivate,
    ) -> Predicates {
        let field = create_value_field(ty.clone())?.lower(encoder);
        let predicate = Predicate::new_struct(ty.lower(encoder), vec![field]);
        Ok(vec![predicate])
    }
}

fn construct_never_predicate(encoder: &impl HighTypeEncoderInterfacePrivate) -> Predicates {
    let predicate = Predicate::new_abstract(vir_high::Type::Never.lower(encoder));
    Ok(vec![predicate])
}

impl IntoPredicates for vir_high::type_decl::Closure {
    fn lower(
        &self,
        ty: &vir_high::Type,
        encoder: &impl HighTypeEncoderInterfacePrivate,
    ) -> Predicates {
        let predicate = Predicate::new_struct(ty.lower(encoder), vec![]);
        Ok(vec![predicate])
    }
}

impl IntoPredicates for vir_high::type_decl::Unsupported {
    fn lower(
        &self,
        ty: &vir_high::Type,
        encoder: &impl HighTypeEncoderInterfacePrivate,
    ) -> Predicates {
        let predicate = Predicate::new_abstract(ty.lower(encoder));
        Ok(vec![predicate])
    }
}
