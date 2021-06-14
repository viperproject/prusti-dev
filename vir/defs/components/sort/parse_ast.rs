pub enum Sort {
    Bool,
    Int,
    Real,
    /// A user-defined uninterpreted sort.
    Uninterpreted {
        name: syn::Ident,
    },
}
