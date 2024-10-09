use syn::punctuated::Punctuated;

/// Determines how data should be treated during reification, as well as
/// de/serialisation.
pub(crate) enum ReifyKind {
    // There is no `ReifyString`, since there is nothing to reify.

    /// String reference, `&'vir str`.
    ///
    /// Reify: passthrough.
    ///   Ser: serialise as `String`.
    //  Deser: allocate into arena.
    PassString,

    /// Slice of a reifiable type, e.g. `&'vir [Expr<'vir>]`.
    ///
    /// Reify: reify every element.
    ///   Ser: serialise every element as owned data.
    /// Deser: allocate every element into arena.
    ReifySlice,

    /// Slice of a non-refiable type, e.g. `&'vir [LocalDecl<'vir>]`.
    ///
    /// Reify: passthrough.
    ///   Ser: serialise every element as owned data.
    /// Deser: allocate every element into arena.
    PassSlice,

    /// Option of a reifiable type, e.g. `Option<Expr<'vir>>`.
    ///
    /// Reify: reify value, if present.
    ///   Ser: serialise value as owned data, if present.
    /// Deser: allocate value into arena.
    ReifyOption,

    /// Option of a non-reifiable type, e.g. `Option<VirSpan<'vir>>`.
    ///
    /// Reify: passthrough.
    ///   Ser: serialise value as owned data, if present.
    /// Deser: allocate value into arena.
    PassOption,

    /// Reifiable owned type.
    ///
    /// Reify: reify value.
    ///   Ser: default serde implementation.
    /// Deser: default serde implementation.
    ReifyOwned,

    /// Non-reifiable owned type.
    ///
    /// Reify: passthrough.
    ///   Ser: default serde implementation.
    /// Deser: default serde implementation.
    PassOwned,

    /// Reference to a non-reifiable type.
    ///
    /// Reify: passthrough.
    ///   Ser: serialise as owned data.
    /// Deser: allocate value into arena.
    PassRef,
}

impl ReifyKind {
    pub(crate) fn of_field(field: &syn::Field) -> ReifyKind {
        // parse flags from `#[vir(..)]` attributes
        enum VirFlag {
            ReifyPass,
            IsRef,
        }
        let flags = field.attrs.iter()
            .filter(|attr| match &attr.meta {
                syn::Meta::List(l) => l.path.segments.len() == 1 && l.path.segments[0].ident == "vir",
                _ => false,
            })
            .flat_map(|attr| attr.parse_args_with(Punctuated::<syn::Ident, syn::Token![,]>::parse_terminated)
                .expect("invalid vir attribute arguments")
                .into_iter())
            .map(|ident| match ident.to_string().as_str() {
                "reify_pass" => VirFlag::ReifyPass,
                "is_ref" => VirFlag::IsRef,
                _ => panic!("invalid vir flag: {ident}"),
            })
            .collect::<Vec<_>>();
        let is_reify_pass = flags.iter().any(|flag| matches!(flag, VirFlag::ReifyPass));
        let is_ref = flags.iter().any(|flag| matches!(flag, VirFlag::IsRef));

        // is this a string? `&'vir str`
        if matches!(&field.ty, syn::Type::Reference(syn::TypeReference {
            mutability: None,
            elem: box syn::Type::Path(syn::TypePath {
                qself: None,
                path: syn::Path {
                    leading_colon: None,
                    segments,
                },
            }),
            ..
        }) if segments.len() == 1 && matches!(&segments[0], syn::PathSegment {
            ident,
            arguments: syn::PathArguments::None,
        } if ident == "str")) {
            assert!(!is_ref, "invalid flag on string: is_ref");
            assert!(!is_reify_pass, "invalid flag on string: is_reify_pass");
            return ReifyKind::PassString;
        }

        // is this a slice? `&'vir [..]`
        if matches!(&field.ty, syn::Type::Reference(syn::TypeReference {
            mutability: None,
            elem: box syn::Type::Slice(_),
            ..
        })) {
            assert!(!is_ref, "invalid flag on slice: is_ref");
            if is_reify_pass {
                return ReifyKind::PassSlice;
            } else {
                return ReifyKind::ReifySlice;
            }
        }

        // is this an option? `Option<..>`
        if matches!(&field.ty, syn::Type::Path(syn::TypePath {
            qself: None,
            path: syn::Path {
                leading_colon: None,
                segments,
            },
        }) if segments.len() == 1 && matches!(&segments[0], syn::PathSegment {
            ident,
            arguments: syn::PathArguments::AngleBracketed(..),
        } if ident == "Option")) {
            assert!(!is_ref, "invalid flag on Option: is_ref");
            if is_reify_pass {
                return ReifyKind::PassOption;
            } else {
                return ReifyKind::ReifyOption;
            }
        }

        if is_reify_pass {
            if is_ref {
                ReifyKind::PassRef
            } else {
                ReifyKind::PassOwned
            }
        } else {
            assert!(!is_ref);
            ReifyKind::ReifyOwned
        }
    }

    /// Should `reify` be called on this field when reifying its container?
    pub(crate) fn should_reify(&self) -> bool {
        matches!(self, Self::ReifySlice | Self::ReifyOption | Self::ReifyOwned)
    }
}
