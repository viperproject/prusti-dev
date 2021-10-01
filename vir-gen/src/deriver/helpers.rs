use syn::{parse_quote, spanned::Spanned};

use crate::helpers::method_name_from_camel;

pub(super) struct DeriveInfo {
    enum_ident: syn::Ident,
    variants: Vec<syn::Variant>,
}

pub(super) fn collect(items: &mut [syn::Item]) -> Vec<DeriveInfo> {
    let mut helpers_to_derive = Vec::new();
    for item in items {
        match item {
            syn::Item::Enum(enum_item) => {
                if let Some(pos) = enum_item
                    .attrs
                    .iter()
                    .position(|attr| attr.path.is_ident("derive_helpers"))
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

pub(super) fn derive(
    mut items: Vec<syn::Item>,
    helpers_to_derive: Vec<DeriveInfo>,
) -> Result<Vec<syn::Item>, syn::Error> {
    for DeriveInfo {
        enum_ident,
        variants,
    } in helpers_to_derive
    {
        let mut helpers: Vec<syn::ImplItem> = Vec::new();
        for variant in variants {
            let variant_type = {
                match &variant.fields {
                    syn::Fields::Unnamed(fields) if fields.unnamed.len() == 1 => {
                        match &fields.unnamed[0].ty {
                            syn::Type::Path(syn::TypePath { qself: None, path }) => path,
                            _ => {
                                return Err(syn::Error::new(
                                    variant.span(),
                                    "unsupported field shape for deriving helpers",
                                ));
                            }
                        }
                    }
                    _ => {
                        return Err(syn::Error::new(
                            variant.span(),
                            "unsupported variant shape for deriving helpers",
                        ));
                    }
                }
            };
            let variant_struct = {
                let item = items
                    .iter()
                    .find(|item| {
                        if let syn::Item::Struct(struct_item) = item {
                            variant_type.is_ident(&struct_item.ident)
                        } else {
                            false
                        }
                    })
                    .ok_or_else(|| syn::Error::new(variant_type.span(), "not found variant"))?;
                if let syn::Item::Struct(struct_item) = item {
                    struct_item
                } else {
                    return Err(syn::Error::new(
                        variant_type.span(),
                        "variant is not struct",
                    ));
                }
            };
            let method_name = method_name_from_camel(&variant.ident);
            let variant_ident = &variant.ident;
            let variant_struct_ident = &variant_struct.ident;
            let parameters: Vec<syn::FnArg> = variant_struct
                .fields
                .iter()
                .map(|field| {
                    let name = field.ident.as_ref().unwrap();
                    let ty = &field.ty;
                    parse_quote!(
                        #name: #ty
                    )
                })
                .collect();
            let fields: Vec<syn::Ident> = variant_struct
                .fields
                .iter()
                .map(|field| field.ident.as_ref().unwrap().clone())
                .collect();
            let method = parse_quote! {
                pub fn #method_name(#(#parameters),*) -> #enum_ident {
                    #enum_ident::#variant_ident(#variant_struct_ident {
                        #(#fields),*
                    })
                }
            };
            helpers.push(method);
        }
        let enum_impl = parse_quote! {
            impl #enum_ident {
                #(#helpers)*
            }
        };
        items.push(enum_impl);
    }
    Ok(items)
}
