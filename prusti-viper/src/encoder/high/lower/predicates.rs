use super::super::types::{create_value_field, interface::HighTypeEncoderInterfacePrivate};
use crate::encoder::{errors::EncodingResult, high::lower::IntoPolymorphic};
use vir_crate::{
    high as vir_high,
    polymorphic::{self as vir_poly, ExprIterator},
};
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
            vir_high::TypeDecl::Float(ty_decl) => ty_decl.lower(ty, encoder),
            vir_high::TypeDecl::TypeVar(ty_decl) => ty_decl.lower(ty, encoder),
            vir_high::TypeDecl::Tuple(ty_decl) => ty_decl.lower(ty, encoder),
            vir_high::TypeDecl::Struct(ty_decl) => ty_decl.lower(ty, encoder),
            vir_high::TypeDecl::Enum(ty_decl) => ty_decl.lower(ty, encoder),
            vir_high::TypeDecl::Union(_ty_decl) => unreachable!("Unions are not supported"),
            vir_high::TypeDecl::Array(ty_decl) => ty_decl.lower(ty, encoder),
            vir_high::TypeDecl::Sequence(_ty_decl) => unimplemented!(),
            vir_high::TypeDecl::Map(_ty_decl) => unimplemented!(),
            vir_high::TypeDecl::Reference(ty_decl) => ty_decl.lower(ty, encoder),
            vir_high::TypeDecl::Pointer(ty_decl) => ty_decl.lower(ty, encoder),
            vir_high::TypeDecl::Never => construct_never_predicate(encoder),
            vir_high::TypeDecl::Closure(ty_decl) => ty_decl.lower(ty, encoder),
            vir_high::TypeDecl::Unsupported(ty_decl) => ty_decl.lower(ty, encoder),
            vir_high::TypeDecl::Trusted(_ty_decl) => {
                unreachable!("Trusted types are not supported")
            }
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

impl IntoPredicates for vir_high::type_decl::Float {
    fn lower(
        &self,
        ty: &vir_high::Type,
        encoder: &impl HighTypeEncoderInterfacePrivate,
    ) -> Predicates {
        let field = create_value_field(ty.clone())?.lower(encoder);
        let predicate = Predicate::new_primitive_value(ty.lower(encoder), field, None, None);
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
                vir_high::FieldDecl::new(field_name, field_num, ty.clone()).lower(encoder)
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

        let discriminant_field =
            vir_high::FieldDecl::discriminant(vir_high::Type::MInt).lower(encoder);
        let this = Predicate::construct_this(lower_type);
        let discriminant_loc = vir_poly::Expr::from(this.clone()).field(discriminant_field.clone());

        let mut variants = Vec::new();
        for (variant, discriminant) in self.variants.iter().zip(self.discriminant_values.clone()) {
            let guard = vir_poly::Expr::eq_cmp(discriminant_loc.clone(), discriminant.into());
            let variant_ty = ty.clone().variant(variant.name.clone().into());
            let predicate = lower_struct(variant, &variant_ty, encoder)?;
            variants.push((guard, variant.name.clone(), predicate));
        }
        let mut predicates: Vec<_> = variants
            .iter()
            .filter(|(_, _, predicate)| !predicate.has_empty_body())
            .map(|(_, _, predicate)| Predicate::Struct(predicate.clone()))
            .collect();
        let discriminant_bounds = self
            .discriminant_bounds
            .iter()
            .map(|&(from, to)| {
                if from == to {
                    vir_poly::Expr::eq_cmp(discriminant_loc.clone(), from.into())
                } else {
                    vir_poly::Expr::and(
                        vir_poly::Expr::le_cmp(from.into(), discriminant_loc.clone()),
                        vir_poly::Expr::le_cmp(discriminant_loc.clone(), to.into()),
                    )
                }
            })
            .disjoin();
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

impl IntoPredicates for vir_high::type_decl::Pointer {
    fn lower(
        &self,
        ty: &vir_high::Type,
        encoder: &impl HighTypeEncoderInterfacePrivate,
    ) -> Predicates {
        // Pointers are unsupported.
        let predicate = Predicate::new_abstract(ty.lower(encoder));
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
        let fields = self
            .arguments
            .iter()
            .enumerate()
            .map(|(field_num, ty)| {
                let field_name = format!("closure_{}", field_num);
                vir_high::FieldDecl::new(field_name, field_num, ty.clone()).lower(encoder)
            })
            .collect();
        let predicate = Predicate::new_struct(ty.lower(encoder), fields);
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
