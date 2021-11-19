use quote::quote;
use syn::{parse_quote, spanned::Spanned};
use crate::{ast::PathList, helpers::unbox_type};

pub(super) fn derive(items: &mut Vec<syn::Item>, current_path: &[syn::Ident]) -> Result<(), syn::Error> {
    let mut derived_items = Vec::new();
    for item in items.iter_mut() {
        if let syn::Item::Struct(struct_item) = item {
            let mut new_attributes = Vec::new();
            let mut from_type_roots = Vec::new();
            for attribute in struct_item.attrs.drain(..) {
                if attribute.style == syn::AttrStyle::Outer && attribute.path.is_ident("derive") {
                    let paths = syn::parse2::<PathList>(attribute.tokens.clone())?.paths;
                    if paths.len() == 1 {
                        let segments = &paths[0].segments;
                        if segments.len() == 1 {
                            if &segments[0].ident == "identity_from" {
                                if let syn::PathArguments::AngleBracketed(syn::AngleBracketedGenericArguments{args, ..}) = &segments[0].arguments {
                                    if args.len() == 1 {
                                        if let syn::GenericArgument::Type(syn::Type::Path(syn::TypePath {qself: None, path: from_type_root})) = &args[0] {
                                            from_type_roots.push(from_type_root.clone());
                                            continue;
                                        }else {
                                            return Err(syn::Error::new(segments[0].span(), "the argument should be a path"));
                                        }
                                    } else {
                                        return Err(syn::Error::new(segments[0].span(), "wrong number of arguments"));
                                    }
                                } else {
                                    return Err(syn::Error::new(segments[0].span(), "wrong path argument"));
                                }
                            }
                        }
                    }
                }
                new_attributes.push(attribute);
            }
            struct_item.attrs = new_attributes;
            for from_type_root in from_type_roots {
                let derived_item = derive_from(&struct_item, from_type_root, current_path);
                derived_items.push(derived_item);
            }
        }
    }
    items.extend(derived_items);
    Ok(())
}

fn derive_from(target_type: &syn::ItemStruct, from_type_root: syn::Path, current_path: &[syn::Ident]) -> syn::Item {
    assert!(from_type_root.leading_colon.is_none());
    let mut current_path = current_path.iter();
    let mut final_from_type_root = Vec::new();
    for segment in from_type_root.segments {
        if segment.ident == "super" {
            current_path.next().unwrap();
        } else {
            final_from_type_root.push(segment.ident);
        }
    }

    let struct_ident = &target_type.ident;
    let from_type: syn::Type = parse_quote! {
        #(#final_from_type_root)::* :: #(#current_path)::* :: #struct_ident
    };
    let mut fields = Vec::<syn::FieldValue>::new();
    for field in &target_type.fields {
        let name = field.ident.as_ref().unwrap();
        if unbox_type(&field.ty) == field.ty {
            fields.push(parse_quote!(
                #name: value.#name.into()
            ));
        } else {
            fields.push(parse_quote!(
                #name: Box::new((*value.#name).into())
            ));
        }
    }
    parse_quote! {
        impl From<#from_type> for #struct_ident {
            fn from(value: #from_type) -> Self {
                Self {
                    #(#fields),*
                }
            }
        }
    }
}