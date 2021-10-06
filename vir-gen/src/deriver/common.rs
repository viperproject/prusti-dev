use syn::spanned::Spanned;

pub(super) struct DeriveInfo {
    pub(super) enum_ident: syn::Ident,
    pub(super) variants: Vec<syn::Variant>,
}

pub(super) fn collect(items: &mut [syn::Item], macro_name: &str) -> Vec<DeriveInfo> {
    let mut helpers_to_derive = Vec::new();
    for item in items {
        match item {
            syn::Item::Enum(enum_item) => {
                if let Some(pos) = enum_item
                    .attrs
                    .iter()
                    .position(|attr| attr.path.is_ident(macro_name))
                {
                    enum_item.attrs.remove(pos);
                    let info = DeriveInfo {
                        enum_ident: enum_item.ident.clone(),
                        variants: enum_item.variants.iter().cloned().collect(),
                    };
                    helpers_to_derive.push(info);
                }
            }
            _ => {}
        }
    }
    helpers_to_derive
}

pub(super) fn extract_variant_type(variant: &syn::Variant) -> Result<&syn::Ident, syn::Error> {
    let path = match &variant.fields {
        syn::Fields::Unnamed(fields) if fields.unnamed.len() == 1 => match &fields.unnamed[0].ty {
            syn::Type::Path(syn::TypePath {
                qself: None,
                path:
                    syn::Path {
                        leading_colon: None,
                        segments,
                    },
            }) if segments.len() == 1 => {
                if segments[0].arguments != syn::PathArguments::None {
                    return Err(syn::Error::new(
                        variant.span(),
                        "unsupported field shape for deriving helpers",
                    ));
                }
                &segments[0].ident
            }
            _ => {
                return Err(syn::Error::new(
                    variant.span(),
                    "unsupported field shape for deriving helpers",
                ));
            }
        },
        _ => {
            return Err(syn::Error::new(
                variant.span(),
                "unsupported variant shape for deriving helpers",
            ));
        }
    };
    Ok(path)
}

pub(super) fn find_variant_struct<'a>(
    items: &'a [syn::Item],
    variant_type: &syn::Ident,
) -> Result<&'a syn::ItemStruct, syn::Error> {
    let item = items
        .iter()
        .find(|item| {
            if let syn::Item::Struct(struct_item) = item {
                variant_type == &struct_item.ident
            } else {
                false
            }
        })
        .ok_or_else(|| syn::Error::new(variant_type.span(), "not found variant"))?;
    if let syn::Item::Struct(struct_item) = item {
        Ok(struct_item)
    } else {
        Err(syn::Error::new(
            variant_type.span(),
            "variant is not struct",
        ))
    }
}

pub(super) fn type_to_indent(ty: &syn::Type) -> Result<&syn::Ident, syn::Error> {
    if let syn::Type::Path(syn::TypePath {
        qself: None,
        path: syn::Path {
            leading_colon: None,
            segments,
        },
    }) = ty
    {
        if segments.len() == 1 && segments[0].arguments == syn::PathArguments::None {
            Ok(&segments[0].ident)
        } else {
            Err(syn::Error::new(
                ty.span(),
                &format!("cannot convert {:?} to ident", ty),
            ))
        }
    } else {
        Err(syn::Error::new(
            ty.span(),
            &format!("cannot convert {:?} to ident", ty),
        ))
    }
}

pub(super) fn get_vec_type_arg(ty: &syn::Type) -> Option<&syn::Ident> {
    if let syn::Type::Path(syn::TypePath {
        qself: None,
        path: syn::Path {
            leading_colon: None,
            segments,
        },
    }) = ty
    {
        if segments.len() == 1 && segments[0].ident == "Vec" {
            if let syn::PathArguments::AngleBracketed(syn::AngleBracketedGenericArguments {
                args,
                ..
            }) = &segments[0].arguments
            {
                assert_eq!(args.len(), 1);
                if let syn::GenericArgument::Type(inner_type) = &args[0] {
                    Some(type_to_indent(inner_type).unwrap())
                } else {
                    unreachable!()
                }
            } else {
                unreachable!()
            }
        } else {
            None
        }
    } else {
        None
    }
}
