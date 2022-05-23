//! Encoding of external specs for traits
use crate::{ExternSpecKind, is_predicate_macro, parse_quote_spanned};
use crate::specifications::common::generate_struct_name_for_trait;
use proc_macro2::TokenStream;
use quote::{quote_spanned, ToTokens};
use syn::parse_quote;
use syn::spanned::Spanned;
use super::common::*;

/// Generates a struct for a `syn::ItemTrait` which is used for checking
/// compilation of external specs on traits.
///
/// Given an extern spec for traits
/// ```rust
/// #[extern_spec]
/// trait SomeTrait<T> {
///     fn foo(&self, arg: Self::ArgTy) -> Self::RetTy;
/// }
/// ```
/// it produces a struct
/// ```rust
/// struct Aux<T, TSelf> where TSelf: SomeTrait {
///     // phantom data for T, TSelf
/// }
/// ```
/// and a corresponding impl block with methods of `SomeTrait`.
///
pub fn rewrite_extern_spec(item_trait: &syn::ItemTrait) -> syn::Result<TokenStream> {
    let generated_struct = generate_new_struct(item_trait)?;

    let trait_impl = generated_struct.generate_impl()?;
    let new_struct = generated_struct.generated_struct;
    Ok(quote_spanned! {item_trait.span()=>
        #new_struct
        #trait_impl
    })
}

/// Responsible for generating a struct
fn generate_new_struct(item_trait: &syn::ItemTrait) -> syn::Result<GeneratedStruct> {
    let trait_ident = &item_trait.ident;

    let struct_name = generate_struct_name_for_trait(item_trait);
    let struct_ident = syn::Ident::new(&struct_name, item_trait.span());

    let mut new_struct: syn::ItemStruct = parse_quote_spanned! {item_trait.span()=>
        #[allow(non_camel_case_types)] struct #struct_ident {}
    };

    // Add a new type parameter to struct which represents an implementation of the trait
    let self_type_ident = syn::Ident::new("Prusti_T_Self", item_trait.span());
    new_struct.generics.params.push(syn::GenericParam::Type(
        parse_quote!(#self_type_ident),
    ));

    let parsed_generics = parse_trait_type_params(item_trait)?;
    // Generic type parameters are added as generics to the struct
    for parsed_generic in parsed_generics.iter() {
        if let ProvidedTypeParam::GenericType(type_param) = parsed_generic {
            new_struct.generics.params.push(syn::GenericParam::Type(type_param.clone()));
        }
    }

    let self_type_trait: syn::TypePath = parse_quote_spanned! {item_trait.span()=>
        #trait_ident :: <#(#parsed_generics),*>
    };

    // Add a where clause which restricts this self type parameter to the trait
    if item_trait.generics.where_clause.as_ref().is_some() {
        let span = item_trait.generics.where_clause.as_ref().unwrap().span();
        return Err(syn::Error::new(span, "Where clauses for extern traits specs are not supported"));
    }
    let self_where_clause: syn::WhereClause = parse_quote! {
        where #self_type_ident: #self_type_trait
    };
    new_struct.generics.where_clause = Some(self_where_clause);

    add_phantom_data_for_generic_params(&mut new_struct);

    Ok(GeneratedStruct {
        generated_struct: new_struct,
        item_trait,
        self_type_ident,
        self_type_trait,
    })
}

fn parse_trait_type_params(item_trait: &syn::ItemTrait) -> syn::Result<Vec<ProvidedTypeParam>> {
    let mut result = vec![];
    for generic_param in item_trait.generics.params.iter() {
        if let syn::GenericParam::Type(type_param) = generic_param {
            result.push(
                ProvidedTypeParam::try_parse(type_param)
                    .ok_or_else(|| syn::Error::new(
                        type_param.span(),
                        "Type parameters in external trait specs must be annotated with exactly one of #[generic] or #[concrete]"
                    ))?,
            );
        }
    }
    Ok(result)
}

struct GeneratedStruct<'a> {
    item_trait: &'a syn::ItemTrait,
    self_type_ident: syn::Ident,
    self_type_trait: syn::TypePath,
    generated_struct: syn::ItemStruct,
}

impl<'a> GeneratedStruct<'a> {
    fn generate_impl(&self) -> syn::Result<syn::ItemImpl> {
        // Generate impl block
        let struct_ident = &self.generated_struct.ident;
        let generic_params = self
            .generated_struct
            .generics
            .params
            .clone()
            .into_token_stream();
        let where_clause = self
            .generated_struct
            .generics
            .where_clause
            .clone()
            .into_token_stream();

        let mut struct_impl: syn::ItemImpl = parse_quote_spanned! {self.item_trait.span()=>
            #[allow(non_camel_case_types)]
            impl< #generic_params > #struct_ident < #generic_params > #where_clause {}
        };

        // Add items to impl block
        for trait_item in self.item_trait.items.iter() {
            match trait_item {
                syn::TraitItem::Type(_) => {
                    return Err(syn::Error::new(
                        trait_item.span(),
                        "Associated types in external trait specs should not be declared",
                    ));
                }
                syn::TraitItem::Method(trait_method) => {
                    if trait_method.default.is_some() {
                        return Err(syn::Error::new(
                            trait_method.default.as_ref().unwrap().span(),
                            "Default methods in external trait specs are invalid",
                        ));
                    }

                    let (method, spec_fns) = self.generate_method_stub(trait_method)?;
                    struct_impl.items.push(syn::ImplItem::Method(method));
                    struct_impl.items.extend(spec_fns.into_iter().map(syn::ImplItem::Method));
                },
                syn::TraitItem::Macro(makro) if is_predicate_macro(makro) => {
                    return Err(syn::Error::new(
                        makro.span(),
                        "Can not declare abstract predicate in external spec"
                    ));
                }
                _ => unimplemented!("Unimplemented trait item for extern spec"),
            };
        }

        Ok(struct_impl)
    }

    fn generate_method_stub(&self, trait_method: &syn::TraitItemMethod) -> syn::Result<(syn::ImplItemMethod, Vec<syn::ImplItemMethod>)> {
        let self_type_ident = &self.self_type_ident;
        let self_type_path: syn::TypePath = parse_quote_spanned! {self_type_ident.span()=>
            #self_type_ident
        };

        generate_extern_spec_method_stub(trait_method, &self_type_path, Some(&self.self_type_trait), ExternSpecKind::Trait)
    }
}

#[derive(Debug)]
enum ProvidedTypeParam {
    /// Something non-concrete, i.e. `T`
    ConcreteType(syn::TypeParam),
    /// Something concrete, i.e. `i32`
    GenericType(syn::TypeParam),
}

impl ProvidedTypeParam {
    fn try_parse(from: &syn::TypeParam) -> Option<Self> {
        if from.attrs.len() != 1 {
            return None;
        }

        let path = &from.attrs[0].path;
        if path.segments.len() != 1 {
            return None;
        }

        // Closure for cloning and removing the attrs
        let clone_without_attrs = || {
            let mut cloned = from.clone();
            cloned.attrs.clear();
            cloned
        };

        match path.segments[0].ident.to_string().as_str() {
            "generic" => Some(ProvidedTypeParam::GenericType(clone_without_attrs())),
            "concrete" => Some(ProvidedTypeParam::ConcreteType(clone_without_attrs())),
            _ => None
        }
    }
}

impl ToTokens for ProvidedTypeParam {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match &self {
            ProvidedTypeParam::ConcreteType(ty_param) |  ProvidedTypeParam::GenericType(ty_param) => ty_param.to_tokens(tokens),
        }
    }
}