use super::common::DeriveInfo;
use crate::{
    deriver::common::{
        extract_variant_type, find_variant_enum, find_variant_struct, get_option_type_arg,
        get_vec_type_arg, type_to_indent,
    },
    helpers::{append_ident, method_name_from_camel, prefixed_method_name_from_camel, unbox_type},
};
use proc_macro2::Span;
use std::collections::HashSet;
use syn::parse_quote;

pub(super) fn derive(
    items: &[syn::Item],
    visitors_to_derive: Vec<DeriveInfo>,
) -> Result<Option<syn::Item>, syn::Error> {
    let mut module_items: Vec<syn::Item> = Vec::new();
    for DeriveInfo {
        enum_ident,
        variants,
    } in visitors_to_derive
    {
        let derivers = [
            Deriver::new(enum_ident.clone(), DeriverKind::Walker),
            Deriver::new(enum_ident.clone(), DeriverKind::Folder),
            Deriver::new(enum_ident.clone(), DeriverKind::FallibleWalker),
            Deriver::new(enum_ident.clone(), DeriverKind::FallibleFolder),
        ];

        for mut deriver in derivers {
            deriver.create_walk_method(&enum_ident, None);
            if deriver.kind.is_folder() {
                deriver.create_boxed_walk_method(&enum_ident);
            }
            deriver.create_default_enum_function(&variants)?;

            let mut all_walked_types = HashSet::new();
            let mut all_created_methods = HashSet::new();
            all_created_methods.insert(enum_ident.clone());

            for variant in &variants {
                if let Some(ty) = extract_variant_type(variant)? {
                    all_created_methods.insert(ty.clone());
                    if deriver.kind.is_folder() {
                        deriver.create_walk_method(ty, Some(variant));
                        deriver.create_boxed_walk_method(ty);
                    } else {
                        deriver.create_walk_method(ty, None);
                    }
                    let walked_types = deriver.create_default_struct_function(items, variant)?;
                    all_walked_types.extend(walked_types);
                } else {
                    deriver.create_argless_walk_method(&variant.ident);
                }
            }
            for ty in all_walked_types.difference(&all_created_methods) {
                deriver.create_empty_walk_method(ty);
            }

            module_items.push(deriver.generate_trait());
            module_items.extend(deriver.default_functions);
        }
    }
    if module_items.is_empty() {
        Ok(None)
    } else {
        Ok(Some(parse_quote! {
            #[allow(clippy::unused_unit, clippy::ptr_arg)]
            pub mod visitors {
                use super::*;
                #(#module_items)*
            }
        }))
    }
}

#[derive(Debug, Clone, Copy)]
enum DeriverKind {
    Walker,
    FallibleWalker,
    Folder,
    FallibleFolder,
}

impl DeriverKind {
    fn is_fallible(&self) -> bool {
        matches!(
            self,
            DeriverKind::FallibleWalker | DeriverKind::FallibleFolder
        )
    }
    fn is_folder(&self) -> bool {
        matches!(self, DeriverKind::Folder | DeriverKind::FallibleFolder)
    }
}

struct Deriver {
    enum_ident: syn::Ident,
    trait_ident: syn::Ident,
    trait_items: Vec<syn::TraitItem>,
    default_functions: Vec<syn::Item>,
    kind: DeriverKind,
}

impl Deriver {
    fn new(enum_ident: syn::Ident, kind: DeriverKind) -> Self {
        let trait_items = if kind.is_fallible() {
            vec![parse_quote! {
                type Error;
            }]
        } else {
            Vec::new()
        };
        Self {
            trait_ident: append_ident(&enum_ident, &format!("{:?}", kind)),
            enum_ident,
            trait_items,
            default_functions: Vec::new(),
            kind,
        }
    }
    fn create_walk_method(&mut self, ty: &syn::Ident, variant: Option<&syn::Variant>) {
        let method_name = self.create_method_name(ty);
        let parameter_name = method_name_from_camel(ty);
        let default_method_name = self.create_default_method_name(ty);
        let parameter_type = self.create_parameter_type(ty);
        let result_type = self.create_result_type(&self.enum_ident, false);
        let call: syn::Expr = parse_quote! {
            #default_method_name(self, #parameter_name)
        };
        let body: syn::Expr = if let Some(variant) = variant {
            let enum_ident = &self.enum_ident;
            let variant_ident = &variant.ident;
            if self.kind.is_fallible() {
                parse_quote! {
                    #call.map(#enum_ident::#variant_ident)
                }
            } else {
                parse_quote! {
                    #enum_ident::#variant_ident(#call)
                }
            }
        } else {
            call
        };
        let method = parse_quote! {
            fn #method_name(&mut self, #parameter_name: #parameter_type) -> #result_type {
                #body
            }
        };
        self.trait_items.push(method);
    }
    fn create_boxed_walk_method(&mut self, ty: &syn::Ident) {
        let method_name = append_ident(&self.create_method_name(ty), "_boxed");
        let parameter_name = method_name_from_camel(ty);
        let default_method_name = self.create_default_method_name(ty);
        let parameter_type = self.create_parameter_type(ty);
        let result_type = self.create_boxed_result_type(ty, false);
        let body: syn::Expr = if self.kind.is_fallible() {
            parse_quote! {
                #default_method_name(self, *#parameter_name).map(Box::new)
            }
        } else {
            parse_quote! {
                Box::new(#default_method_name(self, *#parameter_name))
            }
        };
        let method = parse_quote! {
            #[allow(clippy::boxed_local)]
            fn #method_name(&mut self, #parameter_name: Box<#parameter_type>) -> #result_type {
                #body
            }
        };
        self.trait_items.push(method);
    }
    fn create_argless_walk_method(&mut self, ty: &syn::Ident) {
        let method_name = self.create_method_name(ty);
        let enum_ident = &self.enum_ident;
        let result_type = self.create_result_type(enum_ident, false);
        let result: syn::Expr = match self.kind {
            DeriverKind::Walker => {
                parse_quote! {
                    ()
                }
            }
            DeriverKind::FallibleWalker => {
                parse_quote! {
                    Ok(())
                }
            }
            DeriverKind::Folder => {
                parse_quote! {
                    #enum_ident::#ty
                }
            }
            DeriverKind::FallibleFolder => {
                parse_quote! {
                    Ok(#enum_ident::#ty)
                }
            }
        };
        let method = parse_quote! {
            fn #method_name(&mut self) -> #result_type {
                #result
            }
        };
        self.trait_items.push(method);
    }
    fn create_empty_walk_method(&mut self, ty: &syn::Ident) {
        let method_name = self.create_method_name(ty);
        let parameter_name = prefixed_method_name_from_camel("_", ty);
        let parameter_type = self.create_parameter_type(ty);
        let result_type = self.create_result_type(ty, false);
        let result: syn::Expr = match self.kind {
            DeriverKind::Walker => {
                parse_quote! {
                    ()
                }
            }
            DeriverKind::FallibleWalker => {
                parse_quote! {
                    Ok(())
                }
            }
            DeriverKind::Folder => {
                parse_quote! {
                    #parameter_name
                }
            }
            DeriverKind::FallibleFolder => {
                parse_quote! {
                    Ok(#parameter_name)
                }
            }
        };
        let method = parse_quote! {
            fn #method_name(&mut self, #parameter_name: #parameter_type) -> #result_type {
                #result
            }
        };
        self.trait_items.push(method);
    }
    fn create_default_enum_function(
        &mut self,
        variants: &[syn::Variant],
    ) -> Result<(), syn::Error> {
        let enum_ident = &self.enum_ident;
        let trait_ident = &self.trait_ident;
        let parameter_name = method_name_from_camel(enum_ident);
        let default_method_name = self.create_default_method_name(enum_ident);
        let mut arms: Vec<syn::Arm> = Vec::new();
        for variant in variants {
            let variant_ident = &variant.ident;
            let variant_name = method_name_from_camel(variant_ident);
            let arm = if extract_variant_type(variant)?.is_some() {
                let method_call = self.create_method_call(&variant_name, variant_ident, false);
                parse_quote! {
                    #enum_ident::#variant_ident(#variant_name) => #method_call,
                }
            } else {
                let method_name = self.create_method_name(variant_ident);
                if self.kind.is_fallible() {
                    parse_quote! { #enum_ident::#variant_ident => this.#method_name()?, }
                } else {
                    parse_quote! { #enum_ident::#variant_ident => this.#method_name(), }
                }
            };
            arms.push(arm);
        }
        let parameter_type = self.create_parameter_type(enum_ident);
        let result_type = self.create_result_type(enum_ident, true);
        let result: syn::Expr = if self.kind.is_fallible() {
            parse_quote! {
                Ok(match #parameter_name {
                    #(#arms)*
                })
            }
        } else {
            parse_quote! {
                match #parameter_name {
                    #(#arms)*
                }
            }
        };
        let default_function = parse_quote! {
            #[allow(clippy::unit_arg)]
            pub fn #default_method_name<T: #trait_ident>(this: &mut T, #parameter_name: #parameter_type) -> #result_type {
                #result
            }
        };
        self.default_functions.push(default_function);
        Ok(())
    }
    fn create_default_empty_enum_function(
        &mut self,
        variant: &syn::Variant,
    ) -> Result<Vec<syn::Ident>, syn::Error> {
        let trait_ident = &self.trait_ident;
        let variant_type = extract_variant_type(variant)?.unwrap();
        let parameter_name = method_name_from_camel(variant_type);
        let default_method_name = self.create_default_method_name(variant_type);
        let parameter_type = self.create_parameter_type(variant_type);
        let result_type = self.create_result_type(variant_type, true);
        let result: syn::Expr = match self.kind {
            DeriverKind::Walker => {
                parse_quote! {
                    ()
                }
            }
            DeriverKind::FallibleWalker => {
                parse_quote! {
                    Ok(())
                }
            }
            DeriverKind::Folder => {
                parse_quote! {
                    #parameter_name
                }
            }
            DeriverKind::FallibleFolder => {
                parse_quote! {
                    Ok(#parameter_name)
                }
            }
        };
        let default_function = parse_quote! {
            #[allow(unused_variables)]
            pub fn #default_method_name<T: #trait_ident>(
                this: &mut T,
                #parameter_name: #parameter_type
            ) -> #result_type {
                #result
            }
        };
        self.default_functions.push(default_function);
        Ok(Vec::new())
    }
    fn create_default_struct_function(
        &mut self,
        items: &[syn::Item],
        variant: &syn::Variant,
    ) -> Result<Vec<syn::Ident>, syn::Error> {
        let trait_ident = &self.trait_ident;
        let variant_type = extract_variant_type(variant)?.unwrap();
        if let Some(_variant_enum) = find_variant_enum(items, variant_type) {
            return self.create_default_empty_enum_function(variant);
        }
        let variant_struct = find_variant_struct(items, variant_type)?;
        let parameter_name = method_name_from_camel(variant_type);
        let default_method_name = self.create_default_method_name(variant_type);
        let mut field_names = Vec::<syn::Ident>::new();
        let mut visit_fields = Vec::<syn::Stmt>::new();
        let mut walked_types = Vec::new();
        for field in &variant_struct.fields {
            let name = field.ident.as_ref().unwrap();
            let parameter_type = unbox_type(&field.ty);
            field_names.push(name.clone());

            let statement = if let Some(inner_type) = get_vec_type_arg(&parameter_type) {
                let element = syn::Ident::new("element", Span::call_site());
                let method_call = self.create_method_call(&element, inner_type, false);
                walked_types.push(inner_type.clone());
                if self.kind.is_folder() {
                    parse_quote! {
                        let #name = {
                            let mut new_elements = Vec::new();
                            for element in #name {
                                new_elements.push(#method_call);
                            }
                            new_elements
                        };
                    }
                } else {
                    parse_quote! {
                        for element in #name {
                            #method_call;
                        }
                    }
                }
            } else if let Some(inner_type) = get_option_type_arg(&parameter_type) {
                let element = syn::Ident::new("element", Span::call_site());
                let method_call = self.create_method_call(&element, inner_type, false);
                walked_types.push(inner_type.clone());
                if self.kind.is_folder() {
                    parse_quote! {
                        let #name = if let Some(element) = #name {
                            Some(#method_call)
                        } else {
                            None
                        };
                    }
                } else {
                    parse_quote! {
                        if let Some(element) = #name {
                            #method_call
                        }
                    }
                }
            } else {
                let inner_type = type_to_indent(&parameter_type)?;
                walked_types.push(inner_type.clone());
                let method_call = self.create_method_call(
                    name,
                    inner_type,
                    field.ty != parameter_type && self.kind.is_folder(),
                );
                if self.kind.is_folder() {
                    parse_quote! {
                        let #name = #method_call;
                    }
                } else {
                    parse_quote! {
                        #method_call;
                    }
                }
            };

            visit_fields.push(statement);
        }
        let parameter_type = self.create_parameter_type(variant_type);
        let result_type = self.create_result_type(variant_type, true);
        let result: syn::Expr = match self.kind {
            DeriverKind::Walker => {
                parse_quote! {
                    ()
                }
            }
            DeriverKind::FallibleWalker => {
                parse_quote! {
                    Ok(())
                }
            }
            DeriverKind::Folder => {
                parse_quote! {
                    #variant_type {
                        #(#field_names),*
                    }
                }
            }
            DeriverKind::FallibleFolder => {
                parse_quote! {
                    Ok(#variant_type {
                        #(#field_names),*
                    })
                }
            }
        };
        let default_function = parse_quote! {
            #[allow(clippy::manual_map)]
            pub fn #default_method_name<T: #trait_ident>(this: &mut T, #parameter_name: #parameter_type) -> #result_type {
                let #variant_type {
                    #(#field_names),*
                } = #parameter_name;
                #(#visit_fields)*
                #result
            }
        };
        self.default_functions.push(default_function);
        Ok(walked_types)
    }
    fn create_method_name(&self, ty: &syn::Ident) -> syn::Ident {
        match self.kind {
            DeriverKind::Walker => prefixed_method_name_from_camel("walk_", ty),
            DeriverKind::FallibleWalker => prefixed_method_name_from_camel("fallible_walk_", ty),
            DeriverKind::Folder => prefixed_method_name_from_camel("fold_", ty),
            DeriverKind::FallibleFolder => prefixed_method_name_from_camel("fallible_fold_", ty),
        }
    }
    fn create_method_call(
        &self,
        element: &syn::Ident,
        ty: &syn::Ident,
        unbox_arg: bool,
    ) -> syn::Expr {
        let method_name = self.create_method_name(ty);
        let method_name = if unbox_arg {
            append_ident(&method_name, "_boxed")
        } else {
            method_name
        };
        if self.kind.is_fallible() {
            parse_quote! { this.#method_name(#element)? }
        } else {
            parse_quote! { this.#method_name(#element) }
        }
    }
    fn create_default_method_name(&self, ty: &syn::Ident) -> syn::Ident {
        match self.kind {
            DeriverKind::Walker => prefixed_method_name_from_camel("default_walk_", ty),
            DeriverKind::FallibleWalker => {
                prefixed_method_name_from_camel("default_fallible_walk_", ty)
            }
            DeriverKind::Folder => prefixed_method_name_from_camel("default_fold_", ty),
            DeriverKind::FallibleFolder => {
                prefixed_method_name_from_camel("default_fallible_fold_", ty)
            }
        }
    }
    fn create_result_type(&self, ty: &syn::Ident, in_default: bool) -> syn::Type {
        self.create_result_type_with(syn::parse_quote! { #ty }, in_default)
    }
    fn create_boxed_result_type(&self, ty: &syn::Ident, in_default: bool) -> syn::Type {
        self.create_result_type_with(syn::parse_quote! { Box<#ty> }, in_default)
    }
    fn create_result_type_with(&self, ty: syn::Type, in_default: bool) -> syn::Type {
        match self.kind {
            DeriverKind::Walker => {
                parse_quote! {
                    ()
                }
            }
            DeriverKind::FallibleWalker => {
                if in_default {
                    let trait_ident = &self.trait_ident;
                    parse_quote! {
                        Result<(), <T as #trait_ident>::Error>
                    }
                } else {
                    parse_quote! {
                        Result<(), Self::Error>
                    }
                }
            }
            DeriverKind::Folder => {
                parse_quote! {
                    #ty
                }
            }
            DeriverKind::FallibleFolder => {
                if in_default {
                    let trait_ident = &self.trait_ident;
                    parse_quote! {
                        Result<#ty, <T as #trait_ident>::Error>
                    }
                } else {
                    parse_quote! {
                        Result<#ty, Self::Error>
                    }
                }
            }
        }
    }
    fn create_parameter_type(&self, ty: &syn::Ident) -> syn::Type {
        if self.kind.is_folder() {
            parse_quote! {
                #ty
            }
        } else {
            parse_quote! {
                &#ty
            }
        }
    }
    fn generate_trait(&self) -> syn::Item {
        let trait_ident = &self.trait_ident;
        let trait_items = &self.trait_items;
        parse_quote! {
            pub trait #trait_ident: Sized {
                #(#trait_items)*
            }
        }
    }
}
