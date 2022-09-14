//! Helper functions for creating fields.

use crate::{encoder::errors::EncodingResult, error_internal, error_unsupported};

use vir_crate::high as vir;

#[tracing::instrument(level = "trace")]
pub(crate) fn create_value_field(ty: vir::Type) -> EncodingResult<vir::FieldDecl> {
    let field_decl = match ty {
        vir::Type::Bool => vir::FieldDecl::new("val_bool", 0usize, vir::Type::MBool),

        vir::Type::Int(_) => vir::FieldDecl::new("val_int", 0usize, vir::Type::MInt),

        vir::Type::Float(vir::ty::Float::F32) => {
            vir::FieldDecl::new("val_float32", 0usize, vir::Type::MFloat32)
        }
        vir::Type::Float(vir::ty::Float::F64) => {
            vir::FieldDecl::new("val_float64", 0usize, vir::Type::MFloat64)
        }

        vir::Type::Sequence(ref _seq) => vir::FieldDecl::new("val_seq", 0usize, ty),

        vir::Type::Map(ref _map) => vir::FieldDecl::new("val_map", 0usize, ty),

        // For composed data structures, we typically use a snapshot rather than a field.
        // To unify how parameters are passed to functions, we treat them like a reference.
        vir::Type::Tuple(_)
        | vir::Type::Trusted(_)
        | vir::Type::Struct(_)
        | vir::Type::Enum(_)
        | vir::Type::Closure(_)
        | vir::Type::FunctionDef(_)
        | vir::Type::FnPointer
        | vir::Type::TypeVar(_)
        | vir::Type::Projection(_) => vir::FieldDecl::new("val_ref", 0usize, ty),

        vir::Type::Reference(vir::ty::Reference { target_type, .. }) => {
            vir::FieldDecl::new("val_ref", 0usize, (*target_type).clone())
        }

        vir::Type::Array(_) | vir::Type::Slice(_) => {
            error_internal!("create_value_field should not be called for {}", ty);
        }

        vir::Type::Union(_)
        | vir::Type::Pointer(_)
        | vir::Type::Never
        | vir::Type::Str
        | vir::Type::Unsupported(_) => {
            error_unsupported!("{} type is not supported", ty);
        }

        vir::Type::MBool
        | vir::Type::MInt
        | vir::Type::MFloat32
        | vir::Type::MFloat64
        | vir::Type::MPerm
        | vir::Type::MByte
        | vir::Type::MBytes
        | vir::Type::Lifetime => {
            unreachable!()
        }
    };
    Ok(field_decl)
}
