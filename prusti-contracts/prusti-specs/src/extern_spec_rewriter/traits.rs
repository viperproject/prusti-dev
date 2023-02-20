//! Encoding of external specs for traits
use super::common::*;
use crate::{
    common::SelfTypeRewriter, is_predicate_macro, parse_quote_spanned,
    specifications::common::generate_struct_name_for_trait, ExternSpecKind,
};
use proc_macro2::TokenStream;
use quote::{quote_spanned, ToTokens};
use syn::{parse_quote, spanned::Spanned, TypeParam};

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
pub fn rewrite_extern_spec(
    item_trait: &syn::ItemTrait,
    mod_path: syn::Path,
) -> syn::Result<TokenStream> {
    let mut trait_path = mod_path;
    trait_path.segments.push(syn::PathSegment {
        ident: item_trait.ident.clone(),
        arguments: syn::PathArguments::None,
    });
    let generated_struct = generate_new_struct(item_trait, trait_path)?;

    let trait_impl = generated_struct.generate_impl()?;
    let new_struct = generated_struct.generated_struct;
    Ok(quote_spanned! {item_trait.span()=>
        #new_struct
        #trait_impl
    })
}

/// Responsible for generating a struct
fn generate_new_struct(
    item_trait: &syn::ItemTrait,
    trait_path: syn::Path,
) -> syn::Result<GeneratedStruct> {
    let struct_name = generate_struct_name_for_trait(item_trait);
    let struct_ident = syn::Ident::new(&struct_name, item_trait.span());

    let mut new_struct: syn::ItemStruct = parse_quote_spanned! {item_trait.span()=>
        #[allow(non_camel_case_types)] struct #struct_ident {}
    };

    let new_generics = &mut new_struct.generics.params;

    // Add a new type parameter to struct which represents an implementation of the trait
    let self_type_ident = syn::Ident::new("Prusti_T_Self", item_trait.span());
    new_generics.push(syn::GenericParam::Type(parse_quote!(#self_type_ident)));

    let parsed_generics = parse_trait_type_params(item_trait)?;

    let self_type_trait: syn::TypePath = parse_quote_spanned! {item_trait.span()=>
        #trait_path :: <#(#parsed_generics),*>
    };

    // Generic type parameters are added as generics to the struct
    new_generics.extend(parsed_generics.into_iter().map(syn::GenericParam::Type));

    // Add a where clause which restricts this self type parameter to the trait
    let self_where_clause: syn::WhereClause = if let Some(where_clause) =
        &item_trait.generics.where_clause
    {
        let mut where_clause = where_clause.clone();
        where_clause.rewrite_self_type(&parse_quote! { #self_type_ident }, Some(&self_type_trait));
        // remove trailing comma
        let p = where_clause.predicates.pop().unwrap();
        where_clause.predicates.push(p.into_value());
        // merge into existing where clause
        parse_quote! {
            #where_clause, #self_type_ident: #self_type_trait
        }
    } else {
        parse_quote! {
            where #self_type_ident: #self_type_trait
        }
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

fn parse_trait_type_params(item_trait: &syn::ItemTrait) -> syn::Result<Vec<TypeParam>> {
    item_trait
        .generics
        .type_params()
        .cloned()
        .map(check_for_legacy_attributes)
        .collect()
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
                    if let Some(default) = &trait_method.default {
                        return Err(check_is_stub(default).expect_err("this cannot be a stub"));
                    }

                    let (method, spec_fns) = self.generate_method_stub(trait_method)?;
                    struct_impl.items.push(syn::ImplItem::Method(method));
                    struct_impl
                        .items
                        .extend(spec_fns.into_iter().map(syn::ImplItem::Method));
                }
                syn::TraitItem::Macro(makro) if is_predicate_macro(makro) => {
                    return Err(syn::Error::new(
                        makro.span(),
                        "Can not declare abstract predicate in external spec",
                    ));
                }
                _ => unimplemented!("Unimplemented trait item for extern spec"),
            };
        }

        Ok(struct_impl)
    }

    fn generate_method_stub(
        &self,
        trait_method: &syn::TraitItemMethod,
    ) -> syn::Result<(syn::ImplItemMethod, Vec<syn::ImplItemMethod>)> {
        let self_type_ident = &self.self_type_ident;
        let self_type_path: syn::TypePath = parse_quote_spanned! {self_type_ident.span()=>
            #self_type_ident
        };
        let self_type = syn::Type::Path(self_type_path);

        generate_extern_spec_method_stub(
            trait_method,
            &self_type,
            Some(&self.self_type_trait),
            ExternSpecKind::Trait,
        )
    }
}

fn check_for_legacy_attributes(param: TypeParam) -> syn::Result<TypeParam> {
    if let Some(attr) = param.attrs.first() {
        Err(syn::Error::new(
            attr.span(),
            "The `#[concrete]` and `#[generic]` attributes are deprecated. To refine specs for specific concrete types, use type-conditional spec refinements instead.",
        ))
    } else {
        Ok(param)
    }
}
