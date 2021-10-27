use syn::{parse_quote, spanned::Spanned};

use crate::{ast::PathList, helpers::unbox_type};

pub(super) fn derive(items: &mut Vec<syn::Item>) -> Result<(), syn::Error> {
    let mut derived_items = Vec::new();
    for item in items.iter_mut() {
        if let syn::Item::Struct(struct_item) = item {
            let mut new_attributes = Vec::new();
            for attribute in struct_item.attrs.drain(..) {
                if attribute.style == syn::AttrStyle::Outer && attribute.path.is_ident("derive") {
                    let paths = syn::parse2::<PathList>(attribute.tokens.clone())?.paths;
                    if paths.len() == 1
                        && (paths[0].is_ident("new") || paths[0].is_ident("new_with_pos"))
                    {
                        let constructor = if paths[0].is_ident("new") {
                            derive_new(
                                "new",
                                &struct_item.ident,
                                struct_item.fields.iter(),
                                Some("position"),
                            )
                        } else {
                            derive_new(
                                "new_with_pos",
                                &struct_item.ident,
                                struct_item.fields.iter(),
                                None,
                            )
                        };
                        derived_items.push(constructor);
                        continue;
                    }
                }
                new_attributes.push(attribute);
            }
            struct_item.attrs = new_attributes;
        }
    }
    items.extend(derived_items);
    Ok(())
}

fn derive_new<'a>(
    name: &str,
    struct_ident: &syn::Ident,
    fields_iter: impl Iterator<Item = &'a syn::Field>,
    ignore_field: Option<&str>,
) -> syn::Item {
    let name = syn::Ident::new(name, struct_ident.span());
    let mut parameters = Vec::<syn::FnArg>::new();
    let mut fields = Vec::<syn::FieldValue>::new();
    let mut generics = Vec::<syn::GenericParam>::new();
    for (i, field) in fields_iter.enumerate() {
        let name = field.ident.as_ref().unwrap();
        let parameter_type = unbox_type(&field.ty);
        let generic_type = syn::Ident::new(&format!("G{}", i), parameter_type.span());
        if ignore_field
            .map(|ignored_name| name == ignored_name)
            .unwrap_or(false)
        {
            fields.push(parse_quote!(
                #name: #parameter_type::default()
            ));
        } else {
            generics.push(parse_quote! {
                #generic_type: Into<#parameter_type>
            });
            parameters.push(parse_quote!(
                #name: #generic_type
            ));
            if parameter_type == field.ty {
                fields.push(parse_quote!(
                    #name: #name.into()
                ));
            } else {
                fields.push(parse_quote!(
                    #name: Box::new(#name.into())
                ));
            }
        }
    }
    parse_quote! {
        impl #struct_ident {
            pub fn #name<#(#generics),*>(#(#parameters),*) -> Self {
                Self {
                    #(#fields),*
                }
            }
        }
    }
}
