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
    Unknown
}

impl ExternSpecKind {
    const INHERENT_IMPL_IDENT: &'static str = "inherent_impl";
    const TRAIT_IMPL_IDENT: &'static str = "trait_impl";
    const TRAIT_IDENT: &'static str = "trait";
    const UNKNOWN_IDENT: &'static str = "";
}

impl From<String> for ExternSpecKind {
    fn from(string: String) -> Self {
        match string.as_str() {
            ExternSpecKind::INHERENT_IMPL_IDENT => ExternSpecKind::InherentImpl,
            ExternSpecKind::TRAIT_IMPL_IDENT => ExternSpecKind::TraitImpl,
            ExternSpecKind::TRAIT_IDENT => ExternSpecKind::Trait,
            _ => ExternSpecKind::Unknown
        }
    }
}

impl From<ExternSpecKind> for String {
    fn from(spec_type: ExternSpecKind) -> Self {
        String::from(match spec_type {
            ExternSpecKind::InherentImpl => ExternSpecKind::INHERENT_IMPL_IDENT,
            ExternSpecKind::TraitImpl => ExternSpecKind::TRAIT_IMPL_IDENT,
            ExternSpecKind::Trait => ExternSpecKind::TRAIT_IDENT,
            ExternSpecKind::Unknown => ExternSpecKind::UNKNOWN_IDENT,
        })
    }
}