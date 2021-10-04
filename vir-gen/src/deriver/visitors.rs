use std::collections::HashSet;

use syn::{parse_quote, spanned::Spanned};

use super::common::DeriveInfo;
use crate::{
    deriver::common::{
        extract_variant_type, find_variant_struct, get_vec_type_arg, type_to_indent,
    },
    helpers::{append_ident, method_name_from_camel, prefixed_method_name_from_camel, unbox_type},
};

pub(super) fn derive(
    items: &[syn::Item],
    visitors_to_derive: Vec<DeriveInfo>,
) -> Result<syn::Item, syn::Error> {
    let mut module_items: Vec<syn::Item> = Vec::new();
    for DeriveInfo {
        enum_ident,
        variants,
    } in visitors_to_derive
    {
        let walker_ident = append_ident(&enum_ident, "Walker");
        let mut methods = vec![create_walk_method(&enum_ident)];
        let mut default_functions = vec![create_default_enum_function(
            &enum_ident,
            &variants,
            &walker_ident,
        )];
        let mut all_walked_types = HashSet::new();
        let mut all_created_methods = HashSet::new();
        all_created_methods.insert(enum_ident.clone());
        for variant in variants {
            let ty = extract_variant_type(&variant)?;
            all_created_methods.insert(ty.clone());
            methods.push(create_walk_method(ty));
            let (default_function, walked_types) =
                create_default_struct_function(items, &variant, &walker_ident)?;
            all_walked_types.extend(walked_types);
            default_functions.push(default_function);
        }
        for ty in all_walked_types.difference(&all_created_methods) {
            methods.push(create_empty_walk_method(ty));
        }
        let walker = parse_quote! {
            pub trait #walker_ident: Sized {
                #(#methods)*
            }
        };
        module_items.push(walker);
        module_items.extend(default_functions);
    }
    Ok(parse_quote! {
        pub mod visitors {
            use super::*;
            #(#module_items)*
        }
    })
}

fn create_walk_method(ty: &syn::Ident) -> syn::TraitItem {
    let method_name = prefixed_method_name_from_camel("walk_", ty);
    let parameter_name = method_name_from_camel(ty);
    let default_method_name = prefixed_method_name_from_camel("default_walk_", ty);
    parse_quote! {
        pub fn #method_name(&mut self, #parameter_name: &#ty) {
            #default_method_name(self, #parameter_name);
        }
    }
}

fn create_empty_walk_method(ty: &syn::Ident) -> syn::TraitItem {
    let method_name = prefixed_method_name_from_camel("walk_", ty);
    let parameter_name = prefixed_method_name_from_camel("_", ty);
    parse_quote! {
        pub fn #method_name(&mut self, #parameter_name: &#ty) {
        }
    }
}

fn create_default_enum_function(
    enum_ident: &syn::Ident,
    variants: &[syn::Variant],
    trait_ident: &syn::Ident,
) -> syn::Item {
    let parameter_name = method_name_from_camel(enum_ident);
    let default_method_name = prefixed_method_name_from_camel("default_walk_", enum_ident);
    let mut arms: Vec<syn::Arm> = Vec::new();
    for variant in variants {
        let variant_ident = &variant.ident;
        let method_name = prefixed_method_name_from_camel("walk_", variant_ident);
        let variant_name = method_name_from_camel(variant_ident);
        let arm = parse_quote! {
            #enum_ident::#variant_ident(#variant_name) => this.#method_name(#variant_name),
        };
        arms.push(arm);
    }
    parse_quote! {
        pub fn #default_method_name<T: #trait_ident>(this: &mut T, #parameter_name: &#enum_ident) {
            match #parameter_name {
                #(#arms)*
            }
        }
    }
}

fn create_default_struct_function(
    items: &[syn::Item],
    variant: &syn::Variant,
    trait_ident: &syn::Ident,
) -> Result<(syn::Item, Vec<syn::Ident>), syn::Error> {
    let variant_type = extract_variant_type(&variant)?;
    let variant_struct = find_variant_struct(&items, variant_type)?;
    let parameter_name = method_name_from_camel(variant_type);
    let default_method_name = prefixed_method_name_from_camel("default_walk_", variant_type);
    let mut field_names = Vec::<syn::Ident>::new();
    let mut visit_fields = Vec::<syn::Stmt>::new();
    let mut walked_types = Vec::new();
    for field in &variant_struct.fields {
        let name = field.ident.as_ref().unwrap();
        let parameter_type = unbox_type(&field.ty);
        field_names.push(name.clone());

        let statement = if let Some(inner_type) = get_vec_type_arg(&parameter_type) {
            let method_name = prefixed_method_name_from_camel("walk_", inner_type);
            walked_types.push(inner_type.clone());
            parse_quote! {
                for element in #name {
                    this.#method_name(element);
                }
            }
        } else {
            let inner_type = type_to_indent(&parameter_type)?;
            let method_name = prefixed_method_name_from_camel("walk_", inner_type);
            walked_types.push(inner_type.clone());
            parse_quote! {
                this.#method_name(#name);
            }
        };
        visit_fields.push(statement);
    }
    let function = parse_quote! {
        pub fn #default_method_name<T: #trait_ident>(this: &mut T, #parameter_name: &#variant_type) {
            let #variant_type {
                #(#field_names),*
            } = #parameter_name;
            #(#visit_fields)*
        }
    };
    Ok((function, walked_types))
}
