pub(crate) struct Declarations {
    /// The module that declares the components.
    pub(crate) components: syn::ItemMod,
    /// Modules defining instantiations of IRs.
    pub(crate) irs: Vec<syn::ItemMod>,
}

pub(crate) struct TypeImport {
    /// The imported type.
    pub(crate) name: syn::Ident,
    /// To what this struct should be renamed.
    pub(crate) alias: syn::Ident,
}

/// vir_include!
pub(crate) struct Include {
    /// Path from which we want to include components.
    pub(crate) path: syn::Path,
    /// The list of types to be imported.
    pub(crate) imported_types: Vec<TypeImport>,
    /// The list of derive macros to invoke on each struct and enum.
    pub(crate) derive_macros: Vec<syn::Path>,
}

pub(crate) struct RawBlock {
    /// The name of the block.
    pub(crate) name: syn::Ident,
    /// The contents of the block.
    pub(crate) content: Vec<syn::Item>,
}

/// A list of identifiers
pub(crate) struct IdentList {
    pub(crate) idents: syn::punctuated::Punctuated<syn::Ident, syn::Token![,]>,
}
