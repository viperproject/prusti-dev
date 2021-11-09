use std::collections::HashSet;

use syn::{parse_quote, spanned::Spanned};

use crate::{
    ast::DeriveLower,
    deriver::common::extract_variant_type,
    helpers::{
        extract_container, method_name_from_camel, prefixed_method_name_from_camel,
        prefixed_method_name_from_camel_raw,
    },
};

use super::common::{find_variant_enum, find_variant_struct};

pub(super) fn derive(
    items: &mut Vec<syn::Item>,
    original_irs: &[syn::ItemMod],
) -> Result<(), syn::Error> {
    let mut new_items = Vec::new();
    for item in items.drain(..) {
        match item {
            syn::Item::Macro(macro_item) if macro_item.mac.path.is_ident("derive_lower") => {
                let DeriveLower {
                    user_trait_ident,
                    deriver_trait_ident,
                    mut source_type,
                    mut target_type,
                } = syn::parse2::<DeriveLower>(macro_item.mac.tokens.clone())?;
                let (source_type_module, source_enum) = find_module(original_irs, &source_type)?;
                let (target_type_module, _) = find_module(original_irs, &target_type)?;
                source_type.segments.pop();
                target_type.segments.pop();
                new_items.extend(derive_lowerer(
                    user_trait_ident,
                    deriver_trait_ident,
                    source_type,
                    source_type_module,
                    source_enum,
                    target_type,
                    target_type_module,
                )?);
            }
            _ => {
                new_items.push(item);
            }
        }
    }
    *items = new_items;
    Ok(())
}

fn find_module<'a>(
    original_irs: &'a [syn::ItemMod],
    path: &syn::Path,
) -> Result<(&'a [syn::Item], &'a syn::ItemEnum), syn::Error> {
    for mut current_mod in original_irs {
        let mut segments = path.segments.iter();
        if let Some(first_segment) = segments.next() {
            if first_segment.ident != current_mod.ident {
                continue;
            }
        }
        for (i, segment) in segments.enumerate() {
            let (_, content) = current_mod
                .content
                .as_ref()
                .expect("bug: expander did not expand all modules");
            let mut found = false;
            if i < path.segments.len() - 2 {
                for item in content {
                    if let syn::Item::Mod(module) = item {
                        if module.ident == segment.ident {
                            current_mod = module;
                            found = true;
                            break;
                        }
                    }
                }
                if !found {
                    break;
                }
            } else {
                for item in content {
                    if let syn::Item::Enum(item_enum) = item {
                        if item_enum.ident == segment.ident {
                            return Ok((&current_mod.content.as_ref().unwrap().1, item_enum));
                        }
                    }
                }
            }
        }
    }
    Err(syn::Error::new(path.span(), "not found"))
}

fn derive_lowerer(
    user_trait_ident: syn::Ident,
    deriver_trait_ident: syn::Ident,
    source_path: syn::Path,
    source_type_module: &[syn::Item],
    source_enum: &syn::ItemEnum,
    target_path: syn::Path,
    target_type_module: &[syn::Item],
) -> Result<Vec<syn::Item>, syn::Error> {
    let mut prefix = prefixed_method_name_from_camel_raw("", &user_trait_ident);
    prefix.push('_');
    let mut deriver = Deriver {
        deriver_trait_ident: deriver_trait_ident.clone(),
        user_trait_ident: user_trait_ident.clone(),
        user_trait_method_name: method_name_from_camel(&user_trait_ident),
        prefix,
        queue: vec![WorkItem::RootItem {
            type_ident: source_enum.ident.clone(),
        }],
        done_work_items: HashSet::new(),
        source_path,
        source_type_module,
        target_path,
        target_type_module,
        encoded_methods: Vec::new(),
        encoded_trait_impls: Vec::new(),
    };
    while let Some(work_item) = deriver.queue.pop() {
        if !deriver.done_work_items.contains(&work_item) {
            match &work_item {
                WorkItem::RootItem { type_ident } => {
                    deriver.encode_root_item(type_ident)?;
                }
                WorkItem::EnumVariant {
                    enum_ident,
                    variant_ident,
                    arg_type,
                } => {
                    deriver.encode_enum_variant(enum_ident, variant_ident, arg_type)?;
                }
                WorkItem::Type { ty } => {
                    deriver.encode_type(ty)?;
                }
            }
            deriver.done_work_items.insert(work_item);
        }
    }
    let methods = deriver.encoded_methods;
    let mut items = Vec::new();
    let final_trait = parse_quote! {
        trait #deriver_trait_ident {
            type Error;
            #(#methods)*
        }
    };
    items.push(final_trait);
    let method_name = &deriver.user_trait_method_name;
    let user_trait = parse_quote! {
        trait #user_trait_ident {
            type Output;
            fn #method_name(self, lowerer: &impl #deriver_trait_ident) -> Self::Output;
        }
    };
    items.push(user_trait);
    items.extend(deriver.encoded_trait_impls);
    Ok(items)
}

#[derive(Debug, PartialEq, Eq, Hash)]
enum WorkItem {
    RootItem {
        type_ident: syn::Ident,
    },
    EnumVariant {
        enum_ident: syn::Ident,
        variant_ident: syn::Ident,
        arg_type: Option<syn::Ident>,
    },
    Type {
        ty: Box<syn::Type>,
    },
}

struct Deriver<'a> {
    deriver_trait_ident: syn::Ident,
    user_trait_ident: syn::Ident,
    user_trait_method_name: syn::Ident,
    prefix: String,
    queue: Vec<WorkItem>,
    done_work_items: HashSet<WorkItem>,
    source_path: syn::Path,
    source_type_module: &'a [syn::Item],
    target_path: syn::Path,
    target_type_module: &'a [syn::Item],
    encoded_methods: Vec<syn::Item>,
    encoded_trait_impls: Vec<syn::Item>,
}

impl<'a> Deriver<'a> {
    fn encode_root_item(&mut self, ident: &syn::Ident) -> syn::Result<()> {
        if let Some(source_enum) = find_variant_enum(self.source_type_module, ident) {
            self.encode_enum(ident, source_enum)?;
        } else if let Ok(source_struct) = find_variant_struct(self.source_type_module, ident) {
            self.encode_struct(ident, source_struct)?;
        } else {
            self.encode_stub(ident)?;
        }
        if !self.is_builtin_type(ident) {
            self.encode_user_trait_impl(ident)?;
        }
        Ok(())
    }
    fn encode_name(&self, ident: &syn::Ident) -> syn::Ident {
        prefixed_method_name_from_camel(&self.prefix, ident)
    }
    fn encode_name_nested(&self, outer_ident: &syn::Ident, inner_ident: &syn::Ident) -> syn::Ident {
        let mut prefix = prefixed_method_name_from_camel_raw(&self.prefix, outer_ident);
        prefix.push('_');
        prefixed_method_name_from_camel(&prefix, inner_ident)
    }
    fn encode_variant_method_name(
        &self,
        enum_ident: &syn::Ident,
        variant_ident: &syn::Ident,
    ) -> syn::Ident {
        self.encode_name_nested(enum_ident, variant_ident)
    }
    fn is_builtin_type(&self, ident: &syn::Ident) -> bool {
        matches!(
            ident.to_string().as_str(),
            "String"
                | "bool"
                | "i8"
                | "i16"
                | "i32"
                | "i64"
                | "i128"
                | "u8"
                | "u16"
                | "u32"
                | "u64"
                | "u128"
        )
    }
    fn encode_parameter_type(&self, ident: &syn::Ident) -> syn::Type {
        let path = &self.source_path;
        if self.is_builtin_type(ident) {
            parse_quote! {
                #ident
            }
        } else {
            parse_quote! {
                crate :: #path #ident
            }
        }
    }
    fn encode_return_type(&self, ident: &syn::Ident) -> syn::Type {
        let path = &self.target_path;
        if self.is_builtin_type(ident) {
            parse_quote! {
                #ident
            }
        } else {
            parse_quote! {
                crate :: #path #ident
            }
        }
    }
    fn encode_enum_body(
        &mut self,
        source_enum_type: &syn::Type,
        source_enum: &syn::ItemEnum,
    ) -> syn::Result<syn::Expr> {
        let mut arms = Vec::<syn::Arm>::new();
        for source_variant in &source_enum.variants {
            let source_ident = &source_variant.ident;
            let called_method_name =
                self.encode_variant_method_name(&source_enum.ident, &source_variant.ident);
            let arg_type = if let Some(source_type) = extract_variant_type(source_variant)? {
                let arg = method_name_from_camel(source_type);
                arms.push(parse_quote! {
                    #source_enum_type :: #source_ident (#arg) => { self.#called_method_name(#arg) }
                });
                Some(source_type.clone())
            } else {
                arms.push(parse_quote! {
                    #source_enum_type :: #source_ident => { self.#called_method_name() }
                });
                None
            };
            self.queue.push(WorkItem::EnumVariant {
                enum_ident: source_enum.ident.clone(),
                variant_ident: source_variant.ident.clone(),
                arg_type,
            });
        }
        let expr = parse_quote! {
            match ty {
                #(#arms)*
            }
        };
        Ok(expr)
    }
    fn encode_enum(
        &mut self,
        enum_ident: &syn::Ident,
        source_enum: &syn::ItemEnum,
    ) -> syn::Result<()> {
        let target_enum = find_variant_enum(self.target_type_module, enum_ident);
        let name = self.encode_name(&source_enum.ident);
        let parameter_type = self.encode_parameter_type(enum_ident);
        let return_type = self.encode_return_type(enum_ident);
        let method = if target_enum.is_some() {
            let body = self.encode_enum_body(&parameter_type, source_enum)?;
            parse_quote! {
                fn #name(&self, ty: #parameter_type) -> #return_type {
                    #body
                }
            }
        } else {
            parse_quote! {
                fn #name(&self, ty: #parameter_type) -> #return_type;
            }
        };
        self.encoded_methods.push(method);
        Ok(())
    }
    fn encode_struct(
        &mut self,
        struct_ident: &syn::Ident,
        source_struct: &syn::ItemStruct,
    ) -> syn::Result<()> {
        let target_struct = find_variant_struct(self.target_type_module, struct_ident).ok();
        let name = self.encode_name(struct_ident);
        let parameter_type = self.encode_parameter_type(struct_ident);
        let return_type = self.encode_return_type(struct_ident);
        let method = if target_struct.is_some() {
            let mut fields = Vec::<syn::FieldValue>::new();
            for field in &source_struct.fields {
                let field_name = field.ident.as_ref().unwrap();
                let called_method_name = self.encode_name_by_type(&field.ty)?;
                self.queue.push(WorkItem::Type {
                    ty: Box::new(field.ty.clone()),
                });
                fields.push(parse_quote! {
                    #field_name: self.#called_method_name(ty.#field_name)
                });
            }
            parse_quote! {
                fn #name(&self, ty: #parameter_type) -> #return_type {
                    #return_type {
                        #(#fields),*
                    }
                }
            }
        } else {
            parse_quote! {
                fn #name(&self, ty: #parameter_type) -> #return_type;
            }
        };
        self.encoded_methods.push(method);
        Ok(())
    }
    fn encode_enum_variant(
        &mut self,
        enum_ident: &syn::Ident,
        variant_ident: &syn::Ident,
        arg_type: &Option<syn::Ident>,
    ) -> syn::Result<()> {
        let method_name = self.encode_variant_method_name(enum_ident, variant_ident);
        let return_type = self.encode_return_type(enum_ident);
        let method = if let Some(arg_type) = arg_type {
            let parameter_type = self.encode_parameter_type(arg_type);
            if self.target_has_variant(enum_ident, variant_ident) {
                let called_method_name = self.encode_name(arg_type);
                self.queue.push(WorkItem::RootItem {
                    type_ident: arg_type.clone(),
                });
                parse_quote! {
                    fn #method_name(&self, variant: #parameter_type) -> #return_type {
                        #return_type :: #variant_ident (self.#called_method_name(variant))
                    }
                }
            } else {
                parse_quote! {
                    fn #method_name(&self, variant: #parameter_type) -> #return_type;
                }
            }
        } else {
            parse_quote! {
                fn #method_name(&self) -> #return_type;
            }
        };
        self.encoded_methods.push(method);
        Ok(())
    }
    fn target_has_variant(&self, enum_ident: &syn::Ident, variant_ident: &syn::Ident) -> bool {
        let enum_item = find_variant_enum(self.target_type_module, enum_ident).unwrap();
        enum_item
            .variants
            .iter()
            .any(|variant| &variant.ident == variant_ident)
    }
    fn encode_name_by_type(&self, ty: &syn::Type) -> syn::Result<syn::Ident> {
        let (inner_ident, container_ident) = extract_container(ty)?;
        let name = if let Some(container_ident) = container_ident {
            self.encode_name_nested(container_ident, inner_ident)
        } else {
            self.encode_name(inner_ident)
        };
        Ok(name)
    }

    fn encode_type(&mut self, ty: &syn::Type) -> syn::Result<()> {
        let (inner_ident, container_ident) = extract_container(ty)?;
        self.queue.push(WorkItem::RootItem {
            type_ident: inner_ident.clone(),
        });
        if let Some(container_ident) = container_ident {
            let method_name = self.encode_name_nested(container_ident, inner_ident);
            let parameter_type = self.encode_parameter_type(inner_ident);
            let return_type = self.encode_return_type(inner_ident);
            let method = parse_quote! {
                fn #method_name(&self, #container_ident < #parameter_type >) -> #container_ident < #return_type >;
            };
            self.encoded_methods.push(method);
        }
        Ok(())
    }

    fn encode_stub(&mut self, ident: &syn::Ident) -> syn::Result<()> {
        let method_name = self.encode_name(ident);
        let parameter_type = self.encode_parameter_type(ident);
        let return_type = self.encode_return_type(ident);
        let method = parse_quote! {
            fn #method_name(&self, ty: #parameter_type) -> #return_type;
        };
        self.encoded_methods.push(method);
        Ok(())
    }

    fn encode_user_trait_impl(&mut self, ident: &syn::Ident) -> syn::Result<()> {
        let user_trait_ident = &self.user_trait_ident;
        let deriver_trait_ident = &self.deriver_trait_ident;
        let parameter_type = self.encode_parameter_type(ident);
        let return_type = self.encode_return_type(ident);
        let method_name = &self.user_trait_method_name;
        let called_method_name = self.encode_name(ident);
        let trait_impl = parse_quote! {
            impl #user_trait_ident for #parameter_type {
                type Output = #return_type;
                fn #method_name(self, lowerer: &impl #deriver_trait_ident) -> Self::Output {
                    lowerer.#called_method_name(self)
                }
            }
        };
        self.encoded_trait_impls.push(trait_impl);
        Ok(())
    }
}
