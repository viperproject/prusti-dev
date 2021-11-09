//! Helper functions for creating fields.

use crate::encoder::errors::{EncodingError, EncodingResult};
use log::trace;
use prusti_common::vir::Field;
use vir_crate::high as vir;

pub(crate) fn create_value_field(ty: vir::Type) -> EncodingResult<vir::FieldDecl> {
    trace!("Encode value field for type '{:?}'", ty);
    let field_decl = match ty {
        vir::Type::Bool => vir::FieldDecl::new("val_bool", vir::Type::MBool),

        vir::Type::Int(_) => vir::FieldDecl::new("val_int", vir::Type::MInt),

        // For composed data structures, we typically use a snapshot rather than a field.
        // To unify how parameters are passed to functions, we treat them like a reference.
        vir::Type::Tuple(_)
        | vir::Type::Struct(_)
        | vir::Type::Enum(_)
        | vir::Type::Closure(_)
        | vir::Type::FunctionDef(_)
        | vir::Type::FnPointer => vir::FieldDecl::new("val_ref", ty),

        vir::Type::Reference(vir::ty::Reference { target_type, .. }) => {
            vir::FieldDecl::new("val_ref", (*target_type).clone())
        }

        vir::Type::Array(_) | vir::Type::Slice(_) => {
            return Err(EncodingError::internal(format!(
                "create_value_field should not be called for {}",
                ty
            )));
        }

        vir::Type::TypeVar(_)
        | vir::Type::Union(_)
        | vir::Type::Pointer(_)
        | vir::Type::Never
        | vir::Type::Str
        | vir::Type::Projection(_)
        | vir::Type::Unsupported(_) => {
            return Err(EncodingError::unsupported(format!(
                "{} type is not supported",
                ty
            )));
        }

        vir::Type::MBool | vir::Type::MInt => unreachable!(),
    };
    Ok(field_decl)
}
