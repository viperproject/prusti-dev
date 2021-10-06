use crate::ast::{Include, PathList, RawBlock};
use proc_macro2::TokenStream;
use quote::quote;
use syn::{fold::Fold, parse_quote, spanned::Spanned};

pub(crate) fn expand(
    ir: syn::ItemMod,
    components: &syn::ItemMod,
) -> (syn::ItemMod, Vec<syn::Error>) {
    let mut expander = Expander {
        components,
        errors: Vec::new(),
        new_derives: Vec::new(),
        new_struct_derives: Vec::new(),
    };
    let expanded_ir = expander.fold_item_mod(ir);
    (expanded_ir, expander.errors)
}

struct Expander<'a> {
    components: &'a syn::ItemMod,
    errors: Vec<syn::Error>,
    /// A list of things to derive for each type.
    new_derives: Vec<Vec<syn::Path>>,
    /// A list of things to derive for each struct.
    new_struct_derives: Vec<Vec<syn::Path>>,
}

impl<'a> Expander<'a> {
    fn expand_include(&mut self, items: &mut Vec<syn::Item>, include: Include) -> syn::Result<()> {
        let module = self.find_component(&include.path)?;
        for imported_type in include.imported_types {
            let mut found = false;
            for item in module {
                match item {
                    syn::Item::Struct(syn::ItemStruct { ident, .. })
                    | syn::Item::Enum(syn::ItemEnum { ident, .. })
                    | syn::Item::Trait(syn::ItemTrait { ident, .. })
                        if ident == &imported_type.name =>
                    {
                        let mut item = item.clone();
                        match &mut item {
                            syn::Item::Struct(syn::ItemStruct { ident, attrs, .. })
                            | syn::Item::Enum(syn::ItemEnum { ident, attrs, .. }) => {
                                *ident = imported_type.alias.clone();
                                if !include.derive_macros.is_empty() {
                                    let mut derive_idents = TokenStream::new();
                                    for derive_macro in &include.derive_macros {
                                        derive_idents.extend(quote! {#derive_macro,});
                                    }
                                    attrs.push(parse_quote!(#[derive(#derive_idents)]))
                                }
                            }
                            syn::Item::Trait(syn::ItemTrait { ident, .. }) => {
                                *ident = imported_type.alias.clone();
                            }
                            _ => unreachable!(),
                        }
                        items.push(item);
                        found = true;
                    }
                    syn::Item::Impl(syn::ItemImpl {
                        trait_: Some((_, path, _)),
                        ..
                    }) if path.is_ident(&imported_type.name) => {
                        let mut item = item.clone();
                        match &mut item {
                            syn::Item::Impl(syn::ItemImpl {
                                trait_: Some((_, path, _)),
                                ..
                            }) => {
                                *path = imported_type.alias.clone().into();
                            }
                            _ => unreachable!(),
                        }
                        items.push(item);
                    }
                    syn::Item::Impl(syn::ItemImpl { self_ty, .. }) => match &**self_ty {
                        syn::Type::Path(syn::TypePath { qself: None, path })
                            if path.is_ident(&imported_type.name) =>
                        {
                            let mut item = item.clone();
                            match &mut item {
                                syn::Item::Impl(syn::ItemImpl { self_ty, .. }) => {
                                    *self_ty = Box::new(syn::Type::Path(syn::TypePath {
                                        qself: None,
                                        path: imported_type.alias.clone().into(),
                                    }));
                                }
                                _ => unreachable!(),
                            }
                            items.push(item);
                        }
                        _ => {}
                    },
                    syn::Item::Macro(syn::ItemMacro { mac, .. })
                        if mac.path.is_ident("vir_raw_block") =>
                    {
                        let block = syn::parse2::<RawBlock>(mac.tokens.clone())?;
                        if block.name == imported_type.name {
                            for item in block.content {
                                items.push(item.clone());
                            }
                            found = true;
                        }
                    }
                    _ => {}
                }
            }
            if !found {
                return Err(syn::Error::new(
                    imported_type.name.span(),
                    format!("not found {}", imported_type.name),
                ));
            }
        }
        Ok(())
    }
    fn find_component(&self, path: &syn::Path) -> syn::Result<&[syn::Item]> {
        let mut current_mod = self.components;
        for segment in &path.segments {
            let (_, content) = current_mod
                .content
                .as_ref()
                .expect("bug: expander did not expand all modules");
            let mut found = false;
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
                return Err(syn::Error::new(segment.span(), "not found matching module"));
            }
        }
        let (_, content) = current_mod
            .content
            .as_ref()
            .expect("bug (2): expander did not expand all modules");
        Ok(content)
    }
    /// Add additional `#[derive(...)]` attributes.
    fn add_derives(&self, attributes: &mut Vec<syn::Attribute>, is_struct: bool) {
        let mut new_attributes: Vec<syn::Attribute> = Vec::new();
        for frame in &self.new_derives {
            for derive in frame {
                new_attributes.push(parse_quote! {
                    #[derive(#derive)]
                });
            }
        }
        if is_struct {
            for frame in &self.new_struct_derives {
                for derive in frame {
                    new_attributes.push(parse_quote! {
                        #[derive(#derive)]
                    });
                }
            }
        }
        new_attributes.extend(attributes.drain(..));
        *attributes = new_attributes;
    }
}

impl<'a> Fold for Expander<'a> {
    fn fold_item_mod(&mut self, mut item_mod: syn::ItemMod) -> syn::ItemMod {
        if let Some((brace, content)) = item_mod.content {
            let mut new_attributes = Vec::new();
            let mut new_derives = Vec::new();
            let mut new_struct_derives = Vec::new();
            for attribute in item_mod.attrs {
                match attribute {
                    syn::Attribute {
                        style: syn::AttrStyle::Outer,
                        path,
                        tokens,
                        ..
                    } if path.is_ident("derive_for_all")
                        || path.is_ident("derive_for_all_structs") =>
                    {
                        match syn::parse2::<PathList>(tokens) {
                            Ok(list) => {
                                if path.is_ident("derive_for_all") {
                                    new_derives.extend(list.paths);
                                } else {
                                    new_struct_derives.extend(list.paths);
                                }
                            }
                            Err(error) => {
                                self.errors.push(error);
                            }
                        }
                    }
                    _ => {
                        new_attributes.push(attribute);
                    }
                }
            }
            item_mod.attrs = new_attributes;
            self.new_derives.push(new_derives);
            self.new_struct_derives.push(new_struct_derives);
            let mut new_content = Vec::new();
            for item in content {
                match item {
                    syn::Item::Macro(macro_item) if macro_item.mac.path.is_ident("vir_include") => {
                        match syn::parse2::<Include>(macro_item.mac.tokens) {
                            Ok(include) => {
                                if let Err(error) = self.expand_include(&mut new_content, include) {
                                    self.errors.push(error);
                                }
                            }
                            Err(error) => {
                                self.errors.push(error);
                            }
                        }
                    }
                    _ => {
                        new_content.push(syn::fold::fold_item(self, item));
                    }
                }
            }
            item_mod.content = Some((brace, new_content));
            self.new_derives.pop();
            self.new_struct_derives.pop();
        }
        item_mod
    }
    fn fold_item_enum(&mut self, mut item: syn::ItemEnum) -> syn::ItemEnum {
        self.add_derives(&mut item.attrs, false);
        syn::fold::fold_item_enum(self, item)
    }
    fn fold_item_struct(&mut self, mut item: syn::ItemStruct) -> syn::ItemStruct {
        self.add_derives(&mut item.attrs, true);
        syn::fold::fold_item_struct(self, item)
    }
}
