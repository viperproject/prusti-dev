use crate::helpers::extract_container;
use syn::spanned::Spanned;

pub(super) struct DeriveInfo {
    pub(super) enum_ident: syn::Ident,
    pub(super) variants: Vec<syn::Variant>,
}

pub(super) fn collect(items: &mut [syn::Item], macro_name: &str) -> Vec<DeriveInfo> {
    let mut helpers_to_derive = Vec::new();
    for item in items {
        if let syn::Item::Enum(enum_item) = item {
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
    }
    helpers_to_derive
}

pub(super) fn extract_variant_type(
    variant: &syn::Variant,
) -> Result<Option<&syn::Ident>, syn::Error> {
    let path = match &variant.fields {
        syn::Fields::Unit => None,
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
                Some(&segments[0].ident)
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

pub(super) fn find_variant_enum<'a>(
    items: &'a [syn::Item],
    variant_type: &syn::Ident,
) -> Option<&'a syn::ItemEnum> {
    let item = items.iter().find(|item| {
        if let syn::Item::Enum(enum_item) = item {
            variant_type == &enum_item.ident
        } else {
            false
        }
    });
    if let Some(syn::Item::Enum(enum_item)) = item {
        Some(enum_item)
    } else {
        None
    }
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
        .ok_or_else(|| {
            syn::Error::new(
                variant_type.span(),
                format!("not found variant {variant_type}"),
            )
        })?;
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
                format!("cannot convert {ty:?} to ident"),
            ))
        }
    } else {
        Err(syn::Error::new(
            ty.span(),
            format!("cannot convert {ty:?} to ident"),
        ))
    }
}

pub(super) fn get_option_type_arg(ty: &syn::Type) -> Option<&syn::Ident> {
    let (ident, containers) = extract_container(ty).unwrap();
    if containers.len() == 1 && containers[0] == "Option" {
        Some(ident)
    } else {
        None
    }
}

pub(super) fn get_option_box_type_arg(ty: &syn::Type) -> Option<&syn::Ident> {
    let (ident, containers) = extract_container(ty).unwrap();
    if containers.len() == 2 && containers[0] == "Box" && containers[1] == "Option" {
        Some(ident)
    } else {
        None
    }
}

pub(super) fn get_option_vec_type_arg(ty: &syn::Type) -> Option<&syn::Ident> {
    let (ident, containers) = extract_container(ty).unwrap();
    if containers.len() == 2 && containers[0] == "Vec" && containers[1] == "Option" {
        Some(ident)
    } else {
        None
    }
}

pub(super) fn get_vec_type_arg(ty: &syn::Type) -> Option<&syn::Ident> {
    let (ident, containers) = extract_container(ty).unwrap();
    if containers.len() == 1 && containers[0] == "Vec" {
        Some(ident)
    } else {
        None
    }
}
