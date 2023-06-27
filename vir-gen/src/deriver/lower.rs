use rustc_hash::FxHashSet;

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
                    is_self_mut,
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
                    is_self_mut,
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

#[allow(clippy::too_many_arguments)]
fn derive_lowerer(
    is_self_mut: bool,
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
        is_self_mut,
        deriver_trait_ident: deriver_trait_ident.clone(),
        user_trait_ident: user_trait_ident.clone(),
        user_trait_method_name: method_name_from_camel(&user_trait_ident),
        prefix,
        queue: vec![WorkItem::RootItem {
            type_ident: source_enum.ident.clone(),
        }],
        done_work_items: FxHashSet::default(),
        source_path,
        source_type_module,
        target_path,
        target_type_module,
        encoded_methods: Vec::new(),
        encoded_functions: Vec::new(),
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
    let lowerer_parameter = deriver.encode_lowerer_parameter();
    let methods = deriver.encoded_methods;
    let mut items = Vec::new();
    let final_trait = parse_quote! {
        pub trait #deriver_trait_ident: Sized {
            type Error;
            #(#methods)*
        }
    };
    items.push(final_trait);
    let method_name = &deriver.user_trait_method_name;
    let user_trait = parse_quote! {
        pub trait #user_trait_ident {
            type Output;
            fn #method_name<L: #deriver_trait_ident>(
                self,
                #lowerer_parameter
            ) -> Result<Self::Output, <L as #deriver_trait_ident>::Error>;
        }
    };
    items.push(user_trait);
    items.extend(deriver.encoded_trait_impls);
    items.extend(deriver.encoded_functions);
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
    is_self_mut: bool,
    deriver_trait_ident: syn::Ident,
    user_trait_ident: syn::Ident,
    user_trait_method_name: syn::Ident,
    prefix: String,
    queue: Vec<WorkItem>,
    done_work_items: FxHashSet<WorkItem>,
    source_path: syn::Path,
    source_type_module: &'a [syn::Item],
    target_path: syn::Path,
    target_type_module: &'a [syn::Item],
    encoded_methods: Vec<syn::Item>,
    encoded_functions: Vec<syn::Item>,
    encoded_trait_impls: Vec<syn::Item>,
}

impl<'a> Deriver<'a> {
    fn encode_root_item(&mut self, ident: &syn::Ident) -> syn::Result<()> {
        if let Some(source_enum) = find_variant_enum(self.source_type_module, ident) {
            self.encode_enum(ident, source_enum)?;
        } else if let Ok(source_struct) = find_variant_struct(self.source_type_module, ident) {
            self.encode_struct(ident, source_struct)?;
        } else if self.is_builtin_type(ident) {
            self.encode_builtin(ident)?;
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
    fn encode_default_name(&self, ident: &syn::Ident) -> syn::Ident {
        let prefix = format!("default_{}", self.prefix);
        prefixed_method_name_from_camel(&prefix, ident)
    }
    fn encode_name_nested(&self, outer_ident: &syn::Ident, inner_ident: &syn::Ident) -> syn::Ident {
        let mut prefix = prefixed_method_name_from_camel_raw(&self.prefix, outer_ident);
        prefix.push('_');
        prefixed_method_name_from_camel(&prefix, inner_ident)
    }
    fn encode_name_nested2(
        &self,
        outer_ident1: &syn::Ident,
        outer_ident2: &syn::Ident,
        inner_ident: &syn::Ident,
    ) -> syn::Ident {
        let mut prefix = prefixed_method_name_from_camel_raw(&self.prefix, outer_ident1);
        prefix.push('_');
        prefix = prefixed_method_name_from_camel_raw(&prefix, outer_ident2);
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
                | "isize"
                | "u8"
                | "u16"
                | "u32"
                | "u64"
                | "u128"
                | "usize"
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
                    #source_enum_type :: #source_ident (#arg) => { lowerer.#called_method_name(#arg) }
                });
                Some(source_type.clone())
            } else {
                arms.push(parse_quote! {
                    #source_enum_type :: #source_ident => { lowerer.#called_method_name() }
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
        let self_parameter = self.encode_self_parameter();
        let parameter_type = self.encode_parameter_type(enum_ident);
        let return_type = self.encode_return_type(enum_ident);
        let method = if target_enum.is_some() {
            let body = self.encode_enum_body(&parameter_type, source_enum)?;
            let default_name = self.encode_default_name(&source_enum.ident);
            let lowerer_parameter = self.encode_lowerer_parameter();
            let deriver_trait_ident = &self.deriver_trait_ident;
            let default_function = parse_quote! {
                pub fn #default_name<L: #deriver_trait_ident>(
                    ty: #parameter_type,
                    #lowerer_parameter
                ) -> Result<#return_type, <L as #deriver_trait_ident>::Error> {
                    #body
                }
            };
            self.encoded_functions.push(default_function);
            parse_quote! {
                fn #name(#self_parameter, ty: #parameter_type) -> Result<#return_type, Self::Error> {
                    #default_name(ty, self)
                }
            }
        } else {
            parse_quote! {
                fn #name(#self_parameter, ty: #parameter_type) -> Result<#return_type, Self::Error>;
            }
        };
        self.encoded_methods.push(method);
        Ok(())
    }
    fn structs_match(
        &self,
        source_struct: &syn::ItemStruct,
        target_struct: Option<&syn::ItemStruct>,
    ) -> bool {
        if let Some(target_struct) = target_struct {
            if target_struct.fields.len() != source_struct.fields.len() {
                return false;
            }
            for source_field in &source_struct.fields {
                if !target_struct.fields.iter().any(|target_field| {
                    source_field.ident == target_field.ident && source_field.ty == target_field.ty
                }) {
                    return false;
                }
            }
            true
        } else {
            false
        }
    }
    fn encode_struct(
        &mut self,
        struct_ident: &syn::Ident,
        source_struct: &syn::ItemStruct,
    ) -> syn::Result<()> {
        let target_struct = find_variant_struct(self.target_type_module, struct_ident).ok();
        let name = self.encode_name(struct_ident);
        let self_parameter = self.encode_self_parameter();
        let parameter_type = self.encode_parameter_type(struct_ident);
        let return_type = self.encode_return_type(struct_ident);
        let method = if self.structs_match(source_struct, target_struct) {
            let mut fields = Vec::<syn::FieldValue>::new();
            for field in &source_struct.fields {
                let field_name = field.ident.as_ref().unwrap();
                let called_method_name = self.encode_name_by_type(&field.ty)?;
                self.queue.push(WorkItem::Type {
                    ty: Box::new(field.ty.clone()),
                });
                fields.push(parse_quote! {
                    #field_name: self.#called_method_name(ty.#field_name)?
                });
            }
            let ident: syn::Ident = if fields.is_empty() {
                parse_quote! { _ty }
            } else {
                parse_quote! { ty }
            };
            parse_quote! {
                fn #name(#self_parameter, #ident: #parameter_type) -> Result<#return_type, Self::Error> {
                    Ok(#return_type {
                        #(#fields),*
                    })
                }
            }
        } else {
            parse_quote! {
                fn #name(#self_parameter, ty: #parameter_type) -> Result<#return_type, Self::Error>;
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
        let self_parameter = self.encode_self_parameter();
        let return_type = self.encode_return_type(enum_ident);
        let method = if let Some(arg_type) = arg_type {
            let parameter_type = self.encode_parameter_type(arg_type);
            if self.target_has_variant(enum_ident, variant_ident) {
                let called_method_name = self.encode_name(arg_type);
                self.queue.push(WorkItem::RootItem {
                    type_ident: arg_type.clone(),
                });
                parse_quote! {
                    fn #method_name(#self_parameter, variant: #parameter_type) -> Result<#return_type, Self::Error> {
                        Ok(#return_type :: #variant_ident (self.#called_method_name(variant)?))
                    }
                }
            } else {
                parse_quote! {
                    fn #method_name(#self_parameter, variant: #parameter_type) -> Result<#return_type, Self::Error>;
                }
            }
        } else if self.target_has_variant(enum_ident, variant_ident) {
            parse_quote! {
                fn #method_name(#self_parameter) -> Result<#return_type, Self::Error> {
                    Ok(#return_type::#variant_ident)
                }
            }
        } else {
            parse_quote! {
                fn #method_name(#self_parameter) -> Result<#return_type, Self::Error>;
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
        let (inner_ident, container_idents) = extract_container(ty)?;
        let name = match container_idents.len() {
            0 => self.encode_name(inner_ident),
            1 => self.encode_name_nested(container_idents[0], inner_ident),
            2 => self.encode_name_nested2(container_idents[1], container_idents[0], inner_ident),
            _ => {
                unreachable!();
            }
        };
        Ok(name)
    }

    fn encode_type(&mut self, ty: &syn::Type) -> syn::Result<()> {
        let (inner_ident, mut container_idents) = extract_container(ty)?;
        self.queue.push(WorkItem::RootItem {
            type_ident: inner_ident.clone(),
        });
        if container_idents.is_empty() {
            // nothing to do
        } else if container_idents.len() == 1 {
            let container_ident = container_idents.pop().unwrap();
            let method_name = self.encode_name_nested(container_ident, inner_ident);
            let self_parameter = self.encode_self_parameter();
            let parameter_type = self.encode_parameter_type(inner_ident);
            let return_type = self.encode_return_type(inner_ident);
            let method = if container_ident == "Box" {
                let inner_method_name = self.encode_name(inner_ident);
                parse_quote! {
                    #[allow(clippy::boxed_local)]
                    fn #method_name(#self_parameter, ty: #container_ident < #parameter_type >) -> Result<#container_ident < #return_type >, Self::Error> {
                        Ok(Box::new(self.#inner_method_name(*ty)?))
                    }
                }
            } else if container_ident == "Vec" {
                let inner_method_name = self.encode_name(inner_ident);
                parse_quote! {
                    fn #method_name(#self_parameter, ty: #container_ident < #parameter_type >) -> Result<#container_ident < #return_type >, Self::Error> {
                        ty.into_iter().map(|element| self.#inner_method_name(element)).collect()
                    }
                }
            } else if container_ident == "Option" {
                let inner_method_name = self.encode_name(inner_ident);
                parse_quote! {
                    fn #method_name(#self_parameter, ty: #container_ident < #parameter_type >) -> Result<#container_ident < #return_type >, Self::Error> {
                        ty.map(|element| self.#inner_method_name(element)).transpose()
                    }
                }
            } else {
                parse_quote! {
                    fn #method_name(#self_parameter, _: #container_ident < #parameter_type >) -> Result<#container_ident < #return_type >, Self::Error>;
                }
            };
            self.encoded_methods.push(method);
        } else if container_idents.len() == 2 {
            let container_ident_first = container_idents.pop().unwrap();
            let container_ident_second = container_idents.pop().unwrap();
            let method_name = self.encode_name_nested2(
                container_ident_first,
                container_ident_second,
                inner_ident,
            );
            let self_parameter = self.encode_self_parameter();
            let parameter_type = self.encode_parameter_type(inner_ident);
            let return_type = self.encode_return_type(inner_ident);
            let method = if container_ident_first == "Option" && container_ident_second == "Box" {
                let inner_method_name = self.encode_name(inner_ident);
                parse_quote! {
                    fn #method_name(
                        #self_parameter,
                        ty: #container_ident_first < #container_ident_second < #parameter_type > >
                    ) -> Result< #container_ident_first < #container_ident_second < #return_type > >, Self::Error> {
                        ty.map(|element| self.#inner_method_name(*element).map(Box::new)).transpose()
                    }
                }
            } else if container_ident_first == "Option" && container_ident_second == "Vec" {
                let inner_method_name = self.encode_name(inner_ident);
                parse_quote! {
                    fn #method_name(
                        #self_parameter,
                        ty: #container_ident_first < #container_ident_second < #parameter_type > >
                    ) -> Result< #container_ident_first < #container_ident_second < #return_type > >, Self::Error> {
                        ty.map(|elements|
                            elements.into_iter().map(|element| {
                                self.#inner_method_name(element)
                            }).collect()
                        ).transpose()
                    }
                }
            } else {
                unimplemented!(
                    "first: {} second: {}",
                    container_ident_first,
                    container_ident_second
                );
            };
            self.encoded_methods.push(method);
        } else {
            unimplemented!()
        }

        Ok(())
    }

    fn encode_builtin(&mut self, ident: &syn::Ident) -> syn::Result<()> {
        let method_name = self.encode_name(ident);
        let self_parameter = self.encode_self_parameter();
        let parameter_type = self.encode_parameter_type(ident);
        let method = parse_quote! {
            fn #method_name(#self_parameter, value: #parameter_type) -> Result<#parameter_type, Self::Error> {
                Ok(value)
            }
        };
        self.encoded_methods.push(method);
        Ok(())
    }

    fn encode_stub(&mut self, ident: &syn::Ident) -> syn::Result<()> {
        let method_name = self.encode_name(ident);
        let self_parameter = self.encode_self_parameter();
        let parameter_type = self.encode_parameter_type(ident);
        let return_type = self.encode_return_type(ident);
        let method = parse_quote! {
            fn #method_name(#self_parameter, ty: #parameter_type) -> Result<#return_type, Self::Error>;
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
        let lowerer_parameter = self.encode_lowerer_parameter();
        let trait_impl = parse_quote! {
            impl #user_trait_ident for #parameter_type {
                type Output = #return_type;
                fn #method_name<L: #deriver_trait_ident>(
                    self, #lowerer_parameter
                ) -> Result<Self::Output, <L as #deriver_trait_ident>::Error> {
                    lowerer.#called_method_name(self)
                }
            }
        };
        self.encoded_trait_impls.push(trait_impl);
        let trait_impl_vec = parse_quote! {
            impl #user_trait_ident for Vec<#parameter_type> {
                type Output = Vec<#return_type>;
                fn #method_name<L: #deriver_trait_ident>(
                    self, #lowerer_parameter
                ) -> Result<Self::Output, <L as #deriver_trait_ident>::Error> {
                    let mut elements = Vec::new();
                    for element in self {
                        elements.push(lowerer.#called_method_name(element)?);
                    }
                    Ok(elements)
                }
            }
        };
        self.encoded_trait_impls.push(trait_impl_vec);
        Ok(())
    }

    fn encode_self_parameter(&self) -> syn::FnArg {
        if self.is_self_mut {
            syn::parse_quote! { &mut self }
        } else {
            syn::parse_quote! { &self }
        }
    }

    fn encode_lowerer_parameter(&self) -> syn::FnArg {
        if self.is_self_mut {
            syn::parse_quote! { lowerer: &mut L }
        } else {
            syn::parse_quote! { lowerer: &L }
        }
    }
}
