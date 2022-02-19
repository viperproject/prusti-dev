//! Parsing of `#[extern_spec]` attributed structures

pub mod impls;
pub mod mods;
pub mod traits;
mod common;

#[derive(Debug, Clone, Copy)]
pub enum ExternSpecKind {
    InherentImpl,
    TraitImpl,
    Trait,
    Method,
}

impl ExternSpecKind {
    const INHERENT_IMPL_IDENT: &'static str = "inherent_impl";
    const TRAIT_IMPL_IDENT: &'static str = "trait_impl";
    const TRAIT_IDENT: &'static str = "trait";
    const METHOD_IDENT: &'static str = "method";
}

impl TryFrom<String> for ExternSpecKind {
    type Error = String;

    fn try_from(string: String) -> Result<Self, Self::Error> {
        match string.as_str() {
            Self::INHERENT_IMPL_IDENT => Ok(Self::InherentImpl),
            Self::TRAIT_IMPL_IDENT => Ok(Self::TraitImpl),
            Self::TRAIT_IDENT => Ok(Self::Trait),
            Self::METHOD_IDENT => Ok(Self::Method),
            _ => Err(string),
        }
    }
}

impl From<ExternSpecKind> for String {
    fn from(spec_type: ExternSpecKind) -> Self {
        String::from(match spec_type {
            ExternSpecKind::InherentImpl => ExternSpecKind::INHERENT_IMPL_IDENT,
            ExternSpecKind::TraitImpl => ExternSpecKind::TRAIT_IMPL_IDENT,
            ExternSpecKind::Trait => ExternSpecKind::TRAIT_IDENT,
            ExternSpecKind::Method => ExternSpecKind::METHOD_IDENT,
        })
    }
}
