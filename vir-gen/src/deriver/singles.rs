use crate::{
    ast::{CustomDerive, CustomDeriveList, CustomDeriveOptions},
    helpers::unbox_type,
};
use quote::quote;
use syn::{parse_quote, spanned::Spanned};

pub(super) fn derive(items: &mut Vec<syn::Item>) -> Result<(), syn::Error> {
    let mut derived_items = Vec::new();
    for item in items.iter_mut() {
        match item {
            syn::Item::Struct(struct_item) => {
                let mut new_attributes = Vec::new();
                for attribute in struct_item.attrs.drain(..) {
                    if attribute.style == syn::AttrStyle::Outer && attribute.path.is_ident("derive")
                    {
                        if let Ok(list) = syn::parse2::<CustomDeriveList>(attribute.tokens.clone())
                        {
                            let mut derive_paths = Vec::new();
                            for derive in list.derives {
                                match derive {
                                    CustomDerive::New => derived_items.push(derive_new(
                                        "new",
                                        &struct_item.ident,
                                        struct_item.fields.iter(),
                                        Some("position"),
                                    )),
                                    CustomDerive::NewWithPos => derived_items.push(derive_new(
                                        "new_with_pos",
                                        &struct_item.ident,
                                        struct_item.fields.iter(),
                                        None,
                                    )),
                                    CustomDerive::Hash(options) => derived_items.push(derive_hash(
                                        &struct_item.ident,
                                        struct_item.fields.iter(),
                                        options,
                                    )),
                                    CustomDerive::PartialEq(options) => {
                                        derived_items.push(derive_partial_eq(
                                            &struct_item.ident,
                                            struct_item.fields.iter(),
                                            options,
                                        ))
                                    }
                                    CustomDerive::Ord(options) => {
                                        derived_items.push(derive_ord(
                                            &struct_item.ident,
                                            struct_item.fields.iter(),
                                            options,
                                        ));
                                        derived_items.push(derive_partial_ord(&struct_item.ident));
                                    }
                                    CustomDerive::Other(path) => {
                                        derive_paths.push(path);
                                    }
                                }
                            }
                            if !derive_paths.is_empty() {
                                new_attributes.push(syn::parse_quote! {
                                    #[derive(#(#derive_paths),*)]
                                });
                            }
                            continue;
                        }
                    }
                    new_attributes.push(attribute);
                }
                struct_item.attrs = new_attributes;
            }
            syn::Item::Enum(enum_item) => {
                let mut new_attributes = Vec::new();
                for attribute in enum_item.attrs.drain(..) {
                    if attribute.style == syn::AttrStyle::Outer && attribute.path.is_ident("derive")
                    {
                        if let Ok(list) = syn::parse2::<CustomDeriveList>(attribute.tokens.clone())
                        {
                            let mut derive_paths = Vec::new();
                            for derive in list.derives {
                                match derive {
                                    CustomDerive::New => unimplemented!(),
                                    CustomDerive::NewWithPos => unimplemented!(),
                                    CustomDerive::Hash(_options) => {
                                        derive_paths.push(syn::parse_quote! {Hash});
                                    }
                                    CustomDerive::PartialEq(_options) => {
                                        derive_paths.push(syn::parse_quote! {PartialEq});
                                    }
                                    CustomDerive::Ord(_options) => {
                                        derive_paths.push(syn::parse_quote! {PartialOrd});
                                        derive_paths.push(syn::parse_quote! {Ord});
                                    }
                                    CustomDerive::Other(path) => {
                                        derive_paths.push(path);
                                    }
                                }
                            }
                            if !derive_paths.is_empty() {
                                new_attributes.push(syn::parse_quote! {
                                    #[derive(#(#derive_paths),*)]
                                });
                            }
                            continue;
                        }
                    }
                    new_attributes.push(attribute);
                }
                enum_item.attrs = new_attributes;
            }
            _ => {}
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

fn derive_hash<'a>(
    struct_ident: &syn::Ident,
    fields_iter: impl Iterator<Item = &'a syn::Field>,
    options: CustomDeriveOptions,
) -> syn::Item {
    let mut statements = Vec::<syn::Stmt>::new();
    for field in fields_iter {
        let name = field.ident.as_ref().unwrap();
        if !options.ignored_fields.contains(name) {
            statements.push(parse_quote! {
                self.#name.hash(state);
            });
        }
    }
    parse_quote! {
        impl core::hash::Hash for #struct_ident {
            #[allow(unused_variables)]
            fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
                #(#statements)*
            }
        }
    }
}

fn derive_partial_eq<'a>(
    struct_ident: &syn::Ident,
    fields_iter: impl Iterator<Item = &'a syn::Field>,
    options: CustomDeriveOptions,
) -> syn::Item {
    let mut conjuncts = Vec::<syn::Expr>::new();
    for field in fields_iter {
        let name = field.ident.as_ref().unwrap();
        if !options.ignored_fields.contains(name) {
            conjuncts.push(parse_quote! {
                self.#name == other.#name
            });
        }
    }
    let body = if conjuncts.is_empty() {
        quote! {
            true
        }
    } else {
        quote! {
            #(#conjuncts)&&*
        }
    };
    parse_quote! {
        impl PartialEq for #struct_ident {
            #[allow(unused_variables)]
            fn eq(&self, other: &Self) -> bool {
                #body
            }
        }
    }
}

fn derive_ord<'a>(
    struct_ident: &syn::Ident,
    fields_iter: impl Iterator<Item = &'a syn::Field>,
    options: CustomDeriveOptions,
) -> syn::Item {
    let mut fields_iter = fields_iter.filter(|field| {
        !options
            .ignored_fields
            .contains(field.ident.as_ref().unwrap())
    });
    let comparison = if let Some(first) = fields_iter.next() {
        let name = first.ident.as_ref().unwrap();
        let mut comparison: syn::Expr = syn::parse_quote!( self.#name.cmp(&other.#name) );
        for field in fields_iter {
            let name = field.ident.as_ref().unwrap();
            comparison = syn::parse_quote! {
                #comparison.then(self.#name.cmp(&other.#name))
            };
        }
        comparison
    } else {
        parse_quote! { std::cmp::Ordering::Equal }
    };
    parse_quote! {
        impl Ord for #struct_ident {
            #[allow(unused_variables)]
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                #comparison
            }
        }
    }
}

fn derive_partial_ord(struct_ident: &syn::Ident) -> syn::Item {
    parse_quote! {
        impl PartialOrd for #struct_ident {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }
    }
}
