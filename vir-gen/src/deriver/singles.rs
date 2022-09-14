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
                                    CustomDerive::Hash(options) => {
                                        derived_items.push(derive_hash_for_struct(
                                            &struct_item.ident,
                                            struct_item.fields.iter(),
                                            options,
                                        ))
                                    }
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
                                    CustomDerive::Hash(options) => {
                                        // derive_paths.push(syn::parse_quote! {Hash});
                                        derived_items.push(derive_hash_for_enum(
                                            &enum_item.ident,
                                            enum_item.variants.iter(),
                                            options,
                                        ));
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
        let generic_type = syn::Ident::new(&format!("G{i}"), parameter_type.span());
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
            #[allow(clippy::too_many_arguments)]
            pub fn #name<#(#generics),*>(#(#parameters),*) -> Self {
                Self {
                    #(#fields),*
                }
            }
        }
    }
}

fn derive_hash_for_struct<'a>(
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
    let trait_type = &options.trait_type;
    parse_quote! {
        impl #trait_type for #struct_ident {
            #[allow(unused_variables)]
            fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
                #(#statements)*
            }
        }
    }
}

fn derive_hash_for_enum<'a>(
    struct_ident: &syn::Ident,
    variants_iter: impl Iterator<Item = &'a syn::Variant>,
    options: CustomDeriveOptions,
) -> syn::Item {
    let mut statements = Vec::<syn::Stmt>::new();
    statements.push(parse_quote! {
        let __self_tag = core::mem::discriminant(self);
    });
    statements.push(parse_quote! {
        ::core::hash::Hash::hash(&__self_tag, state);
    });
    let trait_type = &options.trait_type;
    let mut arms = Vec::<syn::Arm>::new();
    for variant in variants_iter {
        let name = &variant.ident;
        match &variant.fields {
            syn::Fields::Named(named_fields) => {
                unimplemented!("named fields not supported yet: {named_fields:?}")
            }
            syn::Fields::Unnamed(unnamed_fields) => {
                let mut arm_idents = Vec::<syn::Ident>::new();
                let mut arm_statements: Vec<syn::Stmt> = Vec::new();
                for (i, field) in unnamed_fields.unnamed.iter().enumerate() {
                    let name = syn::Ident::new(&format!("__self_value_{}", i), field.span());
                    arm_statements.push(parse_quote! {
                        #trait_type::hash(#name, state);
                    });
                    arm_idents.push(name);
                }
                arms.push(parse_quote! {
                    Self::#name(#(#arm_idents),*) => {
                        #(#arm_statements)*
                    }
                });
            }
            syn::Fields::Unit => {
                arms.push(parse_quote! {
                    Self::#name => {}
                });
            }
        }
    }
    if !arms.is_empty() {
        statements.push(parse_quote! {
            match self {
                #(#arms),*
            }
        });
    }
    parse_quote! {
        impl #trait_type for #struct_ident {
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
    let trait_type = &options.trait_type;
    parse_quote! {
        impl #trait_type for #struct_ident {
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
    let trait_type = &options.trait_type;
    parse_quote! {
        impl #trait_type for #struct_ident {
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
