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

/// copy_from!
pub(crate) struct CopyModule {
    /// Path from which we want to include components.
    pub(crate) path: syn::Path,
}

pub(crate) struct RawBlock {
    /// The name of the block.
    pub(crate) name: syn::Ident,
    /// The contents of the block.
    pub(crate) content: Vec<syn::Item>,
}

/// derive_lower!(source_type → target_type)
pub(crate) struct DeriveLower {
    /// Should `&mut self` be used?
    pub(crate) is_self_mut: bool,
    /// The trait that the user can use for lowering.
    pub(crate) user_trait_ident: syn::Ident,
    /// The ident of the trait that needs to be implemented by the deriver struct.
    pub(crate) deriver_trait_ident: syn::Ident,
    /// Path to the type that we want to lower.
    pub(crate) source_type: syn::Path,
    /// Path to the type into which we want to lower.
    pub(crate) target_type: syn::Path,
}

pub(crate) struct CustomDeriveOptions {
    /// The fields that should be ignored when deriving.
    pub(crate) ignored_fields: Vec<syn::Ident>,
}

/// The contents of our custom Derive.
pub(crate) enum CustomDerive {
    New,
    NewWithPos,
    PartialEq(CustomDeriveOptions),
    Hash(CustomDeriveOptions),
    /// PartialOrd is automatically derived to call Ord.
    Ord(CustomDeriveOptions),
    Other(syn::Path),
}

/// A list of identifiers
pub(crate) struct CustomDeriveList {
    pub(crate) derives: syn::punctuated::Punctuated<CustomDerive, syn::Token![,]>,
}
