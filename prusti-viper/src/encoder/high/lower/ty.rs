use super::{super::types::interface::HighTypeEncoderInterfacePrivate, IntoPolymorphic};
use vir_crate::{
    high as vir_high, polymorphic as vir_poly,
    polymorphic::Float::{F32, F64},
};

impl IntoPolymorphic<vir_poly::Type> for vir_high::Type {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::Type {
        encoder.get_interned_lowered_type(self, || match self {
            vir_high::Type::MBool => vir_poly::Type::Bool,
            vir_high::Type::MInt => vir_poly::Type::Int,
            vir_high::Type::MFloat32 => vir_poly::Type::Float(F32),
            vir_high::Type::MFloat64 => vir_poly::Type::Float(F64),
            vir_high::Type::Bool => vir_poly::Type::typed_ref("bool"),
            vir_high::Type::Int(int) => vir_poly::Type::typed_ref(int.to_string().to_lowercase()),
            vir_high::Type::Float(float) => {
                vir_poly::Type::typed_ref(float.to_string().to_lowercase())
            }
            vir_high::Type::TypeVar(ty) => vir_poly::Type::TypeVar(ty.lower(encoder)),
            vir_high::Type::Tuple(ty) => vir_poly::Type::TypedRef(ty.lower(encoder)),
            vir_high::Type::Struct(ty) => vir_poly::Type::TypedRef(ty.lower(encoder)),
            vir_high::Type::Enum(ty) => vir_poly::Type::TypedRef(ty.lower(encoder)),
            vir_high::Type::Union(ty) => vir_poly::Type::TypedRef(ty.lower(encoder)),
            vir_high::Type::Array(ty) => vir_poly::Type::TypedRef(ty.lower(encoder)),
            vir_high::Type::Slice(ty) => vir_poly::Type::TypedRef(ty.lower(encoder)),
            vir_high::Type::Reference(ty) => vir_poly::Type::TypedRef(ty.lower(encoder)),
            vir_high::Type::Pointer(ty) => vir_poly::Type::TypedRef(ty.lower(encoder)),
            vir_high::Type::FnPointer => vir_poly::Type::typed_ref("FnPtr"),
            vir_high::Type::Never => vir_poly::Type::typed_ref("Never"),
            vir_high::Type::Str => vir_poly::Type::typed_ref("Str"),
            vir_high::Type::Closure(ty) => vir_poly::Type::TypedRef(ty.lower(encoder)),
            vir_high::Type::FunctionDef(ty) => vir_poly::Type::TypedRef(ty.lower(encoder)),
            vir_high::Type::Projection(ty) => vir_poly::Type::TypedRef(ty.lower(encoder)),
            vir_high::Type::Unsupported(ty) => vir_poly::Type::TypedRef(ty.lower(encoder)),
        })
    }
}

impl IntoPolymorphic<Vec<vir_poly::Type>> for Vec<vir_high::Type> {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> Vec<vir_poly::Type> {
        self.iter().map(|ty| ty.lower(encoder)).collect()
    }
}

impl IntoPolymorphic<vir_poly::TypeVar> for vir_high::ty::TypeVar {
    fn lower(&self, _encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::TypeVar {
        vir_poly::TypeVar {
            label: self.name.clone(),
        }
    }
}

impl IntoPolymorphic<vir_poly::TypedRef> for vir_high::ty::Tuple {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::TypedRef {
        vir_poly::TypedRef::new("tuple", self.arguments.lower(encoder))
    }
}

impl IntoPolymorphic<vir_poly::TypedRef> for vir_high::ty::Struct {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::TypedRef {
        vir_poly::TypedRef::new(self.name.clone(), self.arguments.lower(encoder))
    }
}

impl IntoPolymorphic<vir_poly::TypedRef> for vir_high::ty::Enum {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::TypedRef {
        vir_poly::TypedRef {
            label: self.name.clone(),
            arguments: self.arguments.lower(encoder),
            variant: self
                .variant
                .as_ref()
                .map(|variant| variant.to_string())
                .unwrap_or_default(),
        }
    }
}

impl IntoPolymorphic<vir_poly::TypedRef> for vir_high::ty::Union {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::TypedRef {
        vir_poly::TypedRef::new(self.name.clone(), self.arguments.lower(encoder))
    }
}

impl IntoPolymorphic<vir_poly::TypedRef> for vir_high::ty::Array {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::TypedRef {
        vir_poly::TypedRef::new(
            format!("Array${}", self.length),
            vec![self.element_type.lower(encoder)],
        )
    }
}

impl IntoPolymorphic<vir_poly::TypedRef> for vir_high::ty::Slice {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::TypedRef {
        vir_poly::TypedRef::new("Slice", vec![self.element_type.lower(encoder)])
    }
}

impl IntoPolymorphic<vir_poly::TypedRef> for vir_high::ty::Reference {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::TypedRef {
        vir_poly::TypedRef::new("ref", vec![self.target_type.lower(encoder)])
    }
}

impl IntoPolymorphic<vir_poly::TypedRef> for vir_high::ty::Pointer {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::TypedRef {
        vir_poly::TypedRef::new("raw_ref", vec![self.target_type.lower(encoder)])
    }
}

impl IntoPolymorphic<vir_poly::TypedRef> for vir_high::ty::Closure {
    fn lower(&self, _encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::TypedRef {
        vir_poly::TypedRef::new(self.name.clone(), Vec::new())
    }
}

impl IntoPolymorphic<vir_poly::TypedRef> for vir_high::ty::FunctionDef {
    fn lower(&self, _encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::TypedRef {
        vir_poly::TypedRef::new(self.name.clone(), Vec::new())
    }
}

impl IntoPolymorphic<vir_poly::TypedRef> for vir_high::ty::Projection {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::TypedRef {
        vir_poly::TypedRef::new(self.name.clone(), self.arguments.lower(encoder))
    }
}

impl IntoPolymorphic<vir_poly::TypedRef> for vir_high::ty::Unsupported {
    fn lower(&self, _encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::TypedRef {
        vir_poly::TypedRef::new(self.name.clone(), Vec::new())
    }
}
