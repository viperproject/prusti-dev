//! Helper functions for creating fields.

use crate::encoder::errors::{EncodingError, EncodingResult};
use log::trace;

use vir_crate::high as vir;

pub(crate) fn create_value_field(ty: vir::Type) -> EncodingResult<vir::FieldDecl> {
    trace!("Encode value field for type '{:?}'", ty);
    let field_decl = match ty {
        vir::Type::Bool => vir::FieldDecl::new("val_bool", vir::Type::MBool),

        vir::Type::Int(_) => vir::FieldDecl::new("val_int", vir::Type::MInt),

        vir::Type::Float(vir::ty::Float::F32) => {
            vir::FieldDecl::new("val_float32", vir::Type::MFloat32)
        }
        vir::Type::Float(vir::ty::Float::F64) => {
            vir::FieldDecl::new("val_float64", vir::Type::MFloat64)
        }

        vir::Type::Sequence(ref _seq) => vir::FieldDecl::new("val_seq", ty),

        vir::Type::Map(ref _map) => vir::FieldDecl::new("val_map", ty),

        // For composed data structures, we typically use a snapshot rather than a field.
        // To unify how parameters are passed to functions, we treat them like a reference.
        vir::Type::Tuple(_)
        | vir::Type::Struct(_)
        | vir::Type::Enum(_)
        | vir::Type::Closure(_)
        | vir::Type::FunctionDef(_)
        | vir::Type::FnPointer
        | vir::Type::TypeVar(_) => vir::FieldDecl::new("val_ref", ty),

        vir::Type::Reference(vir::ty::Reference { target_type, .. }) => {
            vir::FieldDecl::new("val_ref", (*target_type).clone())
        }

        vir::Type::Array(_) | vir::Type::Slice(_) => {
            return Err(EncodingError::internal(format!(
                "create_value_field should not be called for {}",
                ty
            )));
        }

        vir::Type::Union(_)
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

        vir::Type::MBool
        | vir::Type::MInt
        | vir::Type::MFloat32
        | vir::Type::MFloat64
        | vir::Type::Lifetime => {
            unreachable!()
        }
    };
    Ok(field_decl)
}
