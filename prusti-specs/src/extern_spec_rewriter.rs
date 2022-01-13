use super::parse_quote_spanned;
use crate::{span_overrider::SpanOverrider, specifications::common::NameGenerator};
use proc_macro2::{Group, TokenStream, TokenTree};
use quote::{quote, quote_spanned, ToTokens};
use std::collections::HashMap;
use syn::{parse_quote, punctuated::Punctuated, spanned::Spanned};

/// Rewrites every occurence of "self" to "_self" in a token stream
fn rewrite_self(tokens: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let mut new_tokens = proc_macro2::TokenStream::new();
    for token in tokens.into_iter() {
        match token {
            proc_macro2::TokenTree::Group(group) => {
                let new_group =
                    proc_macro2::Group::new(group.delimiter(), rewrite_self(group.stream()));
                new_tokens.extend(new_group.to_token_stream());
            }
            proc_macro2::TokenTree::Ident(mut ident) => {
                if ident == "self" {
                    ident = proc_macro2::Ident::new("_self", ident.span());
                }
                new_tokens.extend(ident.into_token_stream());
            }
            _ => {
                new_tokens.extend(token.into_token_stream());
            }
        }
    }
    new_tokens
}

/// Add `PhantomData` markers for each type parameter to silence errors
/// about unused type parameters.
///
/// Given
/// ```text
/// struct Foo<A,B> {
///    ...fields
/// }
/// ```
/// Result
/// ```text
/// struct Foo<A,B> {
///     ...fields
///     ::core::marker::PhantomData<A>,
///     ::core::marker::PhantomData<B>
/// }
/// ```
fn add_phantom_data_for_generic_params(item_struct: &mut syn::ItemStruct) {
    item_struct.generics = item_struct.generics.clone();
    let generics = &item_struct.generics;

    let mut fields: Vec<syn::Field> = Vec::new();
    for param in generics.params.iter() {
        let field: ParsableUnnamedField = match param {
            syn::GenericParam::Type(tp) => {
                let ident = tp.ident.clone();
                syn::parse_quote! { ::core::marker::PhantomData<#ident> }
            }
            syn::GenericParam::Lifetime(ld) => {
                let ident = ld.lifetime.clone();
                syn::parse_quote! { &#ident ::core::marker::PhantomData<()> }
            }
            syn::GenericParam::Const(_cp) => continue,
        };
        // Unwrap the `ParsableUnnamedField` and push. See below.
        fields.push(field.0);
    }

    item_struct.fields = syn::Fields::Unnamed(syn::parse_quote! { ( #(#fields),* ) });
}

/// The `syn::Field` doesn't implement `syn::parse::Parse` directly since it can do
/// both `parse_unnamed` and `parse_named`. This is a wrapper to tell `parse_quote`
/// to use `parse_unnamed` when parsing. https://github.com/dtolnay/syn/issues/651
struct ParsableUnnamedField(syn::Field);

impl syn::parse::Parse for ParsableUnnamedField {
    fn parse(input: syn::parse::ParseStream<'_>) -> syn::parse::Result<Self> {
        Ok(ParsableUnnamedField(syn::Field::parse_unnamed(input)?))
    }
}

/// We take the Generics (parameters) defined with the `#[extern_spec] impl<...>` (the `<...>`)
/// but then need to pass those as arguments: `SomeStruct<...>`. This function translates from
/// the syntax of one to the other; e.g. `<T: Bound, 'l: Bound, const C: usize>` -> `<T, 'l, C>`
pub fn rewrite_generics(gens: &syn::Generics) -> syn::AngleBracketedGenericArguments {
    let args: Vec<syn::GenericArgument> = gens
        .params
        .clone()
        .into_iter()
        .map(|gp| {
            let ts = match gp {
                syn::GenericParam::Type(syn::TypeParam { ident, .. })
                | syn::GenericParam::Const(syn::ConstParam { ident, .. }) => ident.into_token_stream(),
                syn::GenericParam::Lifetime(ld) => ld.lifetime.into_token_stream(),
            };
            syn::parse2::<syn::GenericArgument>(ts).unwrap()
        })
        .collect();
    syn::parse_quote! { < #(#args),* > }
}

fn rewrite_method_inputs<T: ToTokens>(
    item_ty: &T,
    method_inputs: &mut Punctuated<syn::FnArg, syn::Token![,]>,
) -> syn::punctuated::Punctuated<syn::Expr, syn::token::Comma> {
    let mut args: syn::punctuated::Punctuated<syn::Expr, syn::token::Comma> =
        syn::punctuated::Punctuated::new();
    for input in method_inputs.iter_mut() {
        let input_span = input.span();
        match input {
            syn::FnArg::Receiver(receiver) => {
                let and = if receiver.reference.is_some() {
                    // TODO: do lifetimes need to be specified here?
                    quote_spanned! {input_span=> &}
                } else {
                    quote! {}
                };
                let mutability = &receiver.mutability;
                let fn_arg: syn::FnArg = parse_quote_spanned! {input_span=>
                    _self : #and #mutability #item_ty
                };
                *input = fn_arg;
                let expr: syn::Expr = parse_quote_spanned!(input_span=> _self);
                args.push_value(expr);
            }
            syn::FnArg::Typed(typed) => {
                if let syn::Pat::Ident(ident) = &*typed.pat {
                    let arg = &ident.ident;
                    let expr: syn::Expr = syn::parse_quote!(#arg);
                    args.push_value(expr);
                }
            }
        }
        args.push_punct(syn::token::Comma::default());
    }
    args
}

/// Process external specifications in Rust modules marked with the
/// #[extern_spec] attribute. Nested modules are processed recursively.
/// Specifications are collected from functions and function stubs.
///
/// Modules are rewritten so that their name does not clash with the module
/// they are specifying.
pub mod mods {
    use super::*;

    pub fn rewrite_extern_spec(item_mod: &mut syn::ItemMod) -> syn::Result<TokenStream> {
        let mut path = syn::Path {
            leading_colon: None,
            segments: syn::punctuated::Punctuated::new(),
        };
        rewrite_mod(item_mod, &mut path)?;
        Ok(quote!(#item_mod))
    }

    fn rewrite_mod(item_mod: &mut syn::ItemMod, path: &mut syn::Path) -> syn::Result<()> {
        if item_mod.content.is_none() {
            return Ok(());
        }

        path.segments.push(syn::PathSegment {
            ident: item_mod.ident.clone(),
            arguments: syn::PathArguments::None,
        });
        let name_generator = NameGenerator::new();
        item_mod.ident = syn::Ident::new(
            &name_generator.generate_mod_name(&item_mod.ident),
            item_mod.span(),
        );

        for item in item_mod.content.as_mut().unwrap().1.iter_mut() {
            match item {
                syn::Item::Fn(item_fn) => {
                    rewrite_fn(item_fn, path);
                }
                syn::Item::Mod(inner_mod) => {
                    rewrite_mod(inner_mod, path)?;
                }
                syn::Item::Verbatim(tokens) => {
                    // Transforms function stubs (functions with a `;` after the
                    // signature instead of the body) into functions, then
                    // processes them.
                    let mut new_tokens = TokenStream::new();
                    for mut token in tokens.clone().into_iter() {
                        if let TokenTree::Punct(punct) = &mut token {
                            if punct.as_char() == ';' {
                                new_tokens.extend(
                                    Group::new(proc_macro2::Delimiter::Brace, TokenStream::new())
                                        .to_token_stream(),
                                );
                                continue;
                            }
                        }
                        new_tokens.extend(token.to_token_stream());
                    }
                    let res: Result<syn::Item, _> = syn::parse2(new_tokens);
                    if res.is_err() {
                        return Err(syn::Error::new(item.span(), "invalid function signature"));
                    }

                    let mut item = res.unwrap();
                    if let syn::Item::Fn(item_fn) = &mut item {
                        rewrite_fn(item_fn, path);
                    }
                    *tokens = quote!(#item)
                }
                syn::Item::Use(_) => {}
                _ => return Err(syn::Error::new(item.span(), "unexpected item")),
            }
        }
        Ok(())
    }

    /// Rewrite a specification function to a call to the specified function.
    /// The result of this rewriting is then parsed in `ExternSpecResolver`.
    fn rewrite_fn(item_fn: &mut syn::ItemFn, path: &mut syn::Path) {
        let ident = &item_fn.sig.ident;
        let args = &item_fn.sig.inputs;
        let item_fn_span = item_fn.span();
        item_fn.block = parse_quote_spanned! {item_fn_span=>
            {
                #path :: #ident (#args);
                unimplemented!()
            }
        };

        item_fn
            .attrs
            .push(parse_quote_spanned!(item_fn_span=> #[prusti::extern_spec]));
        item_fn
            .attrs
            .push(parse_quote_spanned!(item_fn_span=> #[trusted]));
    }
}

pub mod impls {
    use super::*;

    pub fn rewrite_extern_spec(item_impl: &mut syn::ItemImpl) -> syn::Result<TokenStream> {
        let new_struct = generate_new_struct(&item_impl)?;
        let struct_ident = &new_struct.ident;
        let generic_args = rewrite_generics(&new_struct.generics);

        let struct_ty: syn::Type = parse_quote_spanned! {item_impl.span()=>
            #struct_ident #generic_args
        };

        let rewritten_item = rewrite_impl(item_impl, Box::from(struct_ty))?;

        Ok(quote_spanned! {item_impl.span()=>
            #new_struct
            #rewritten_item
        })
    }

    fn generate_new_struct(item_struct: &syn::ItemImpl) -> syn::Result<syn::ItemStruct> {
        let name_generator = NameGenerator::new();
        let struct_name = match name_generator.generate_struct_name(item_struct) {
            Ok(name) => name,
            Err(msg) => return Err(syn::Error::new(item_struct.span(), msg)),
        };
        let struct_ident = syn::Ident::new(&struct_name, item_struct.span());

        let mut new_struct: syn::ItemStruct = parse_quote_spanned! {item_struct.span()=>
            #[allow(non_camel_case_types)] struct #struct_ident {}
        };
        new_struct.generics = item_struct.generics.clone();

        add_phantom_data_for_generic_params(&mut new_struct);
        Ok(new_struct)
    }

    /// Rewrite all methods in an impl block to calls to the specified methods.
    /// The result of this rewriting is then parsed in `ExternSpecResolver`.
    fn rewrite_impl(
        impl_item: &mut syn::ItemImpl,
        new_ty: Box<syn::Type>,
    ) -> syn::Result<TokenStream> {
        let item_ty = &mut impl_item.self_ty;
        if let syn::Type::Path(type_path) = item_ty.as_mut() {
            for seg in type_path.path.segments.iter_mut() {
                if let syn::PathArguments::AngleBracketed(genargs) = &mut seg.arguments {
                    genargs.colon2_token = Some(syn::token::Colon2::default());
                }
            }
        }

        for item in impl_item.items.iter_mut() {
            let item_span = item.span();
            match item {
                syn::ImplItem::Method(method) => {
                    for attr in method.attrs.iter_mut() {
                        attr.tokens = rewrite_self(attr.tokens.clone());
                    }

                    let args = rewrite_method_inputs(item_ty, &mut method.sig.inputs);
                    let ident = &method.sig.ident;

                    method
                        .attrs
                        .push(parse_quote_spanned!(item_span=> #[prusti::extern_spec]));
                    method
                        .attrs
                        .push(parse_quote_spanned!(item_span=> #[trusted]));

                    let mut method_path: syn::ExprPath = parse_quote_spanned! {ident.span()=>
                        #item_ty :: #ident
                    };

                    // Fix the span
                    syn::visit_mut::visit_expr_path_mut(
                        &mut SpanOverrider::new(ident.span()),
                        &mut method_path,
                    );

                    method.block = parse_quote_spanned! {item_span=>
                        {
                            #method_path (#args);
                            unimplemented!()
                        }
                    };
                }
                _ => {
                    return Err(syn::Error::new(
                        item.span(),
                        "expected a method".to_string(),
                    ));
                }
            }
        }
        impl_item.self_ty = new_ty;

        Ok(quote! {
            #impl_item
        })
    }
}

/// Rewriting of extern specs on traits
pub mod traits {
    use super::*;

    type AssocTypesToGenericsMap<'a> = HashMap<&'a syn::Ident, syn::TypeParam>;

    /// Generates a struct for a `syn::ItemTrait` which is used for checking
    /// compilation of external specs on traits.
    ///
    /// Given an extern spec for traits
    /// ```rust
    /// #[extern_spec]
    /// trait SomeTrait {
    ///     type ArgTy;
    ///     type RetTy;
    ///
    ///     fn foo(&self, arg: Self::ArgTy) -> Self::RetTy;
    /// }
    /// ```
    /// it produces a struct
    /// ```rust
    /// struct Aux<TSelf, TArgTy, TRetTy> {
    ///     // phantom data for TSelf, TArgTy, TRetTy
    /// }
    /// where TSelf: SomeTrait<ArgTy = TArgTy, RetTy = TRetTy>
    /// ```
    /// and a corresponding impl block with methods of `SomeTrait`.
    ///
    pub fn rewrite_extern_spec(item_trait: &syn::ItemTrait) -> syn::Result<TokenStream> {
        validate_macro_usage(item_trait)?;

        let generated_struct = generate_new_struct(item_trait)?;

        let trait_impl = generated_struct.generate_impl()?;
        let new_struct = generated_struct.generated_struct;
        Ok(quote_spanned! {item_trait.span()=>
                #new_struct
                #trait_impl
        })
    }

    /// Returns an error when the macro was used in a wrong way on the trait
    fn validate_macro_usage(item_trait: &syn::ItemTrait) -> syn::Result<()> {
        // Where clause not supported
        if item_trait.generics.where_clause.as_ref().is_some() {
            let span = item_trait.generics.where_clause.as_ref().unwrap().span();
            return Err(syn::Error::new(span, "Where clauses for extern traits specs are not supported"));
        }

        // Generics not supported
        if item_trait.generics.params.len() > 0 {
            return Err(syn::Error::new(
                item_trait.span(),
                "Generics in external trait specs are not supported",
            ));
        }

        return Ok(());
    }

    /// Responsible for generating a struct
    fn generate_new_struct(item_trait: &syn::ItemTrait) -> syn::Result<GeneratedStruct> {
        let trait_ident = &item_trait.ident;

        let name_generator = NameGenerator::new();
        let struct_name = name_generator.generate_struct_name_for_trait(item_trait);
        let struct_ident = syn::Ident::new(&struct_name, item_trait.span());

        let mut new_struct: syn::ItemStruct = parse_quote_spanned! {item_trait.span()=>
            #[allow(non_camel_case_types)] struct #struct_ident {}
        };
        // Find associated types in trait
        let mut assoc_types_to_generics_map = HashMap::new();
        let associated_type_decls = get_associated_types(item_trait);

        for &decl in associated_type_decls.iter() {
            if decl.default.is_some() {
                return Err(syn::Error::new(decl.span(), "Defaults for an associated types in external trait specs are invalid"));
            }
        }

        for associated_type_decl in associated_type_decls {
            let associated_type_ident = &associated_type_decl.ident;
            let generic_ident = syn::Ident::new(
                format!("Prusti_T_{}", associated_type_ident).as_str(),
                associated_type_ident.span(),
            );
            let type_param: syn::TypeParam =
                parse_quote_spanned! {associated_type_ident.span()=> #generic_ident };
            assoc_types_to_generics_map.insert(associated_type_ident, type_param);
        }

        // Add them as generics
        assoc_types_to_generics_map
            .values()
            .map(|param| syn::GenericParam::Type(param.clone()))
            .for_each(|generic_param| new_struct.generics.params.push(generic_param));

        // Add a new type parameter to struct which represents an implementation of the trait
        let self_type_param_ident = syn::Ident::new("Prusti_T_Self", item_trait.span());
        new_struct.generics.params.push(syn::GenericParam::Type(
            parse_quote!(#self_type_param_ident),
        ));

        // Add a where clause which restricts this self type parameter to the trait
        if item_trait.generics.where_clause.as_ref().is_some() {
            let span = item_trait.generics.where_clause.as_ref().unwrap().span();
            return Err(syn::Error::new(span, "Where clauses for extern traits specs are not supported"));
        }
        let trait_assoc_type_idents = assoc_types_to_generics_map.keys();
        let trait_assoc_type_generics = assoc_types_to_generics_map.values();
        let self_where_clause: syn::WhereClause = parse_quote! {
            where #self_type_param_ident: #trait_ident <#(#trait_assoc_type_idents = #trait_assoc_type_generics),*>
        };
        new_struct.generics.where_clause = Some(self_where_clause);

        add_phantom_data_for_generic_params(&mut new_struct);

        let gen = GeneratedStruct {
            generated_struct: new_struct,
            item_trait,
            assoc_types_to_generics_map,
            self_type_param_ident,
        };
        Ok(gen)
    }

    struct GeneratedStruct<'a> {
        item_trait: &'a syn::ItemTrait,
        assoc_types_to_generics_map: AssocTypesToGenericsMap<'a>,
        self_type_param_ident: syn::Ident,
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
                        // Ignore associated types, they are encoded as generics in the struct
                    }
                    syn::TraitItem::Method(trait_method) => {
                        if trait_method.default.is_some() {
                            return Err(syn::Error::new(
                                trait_method.default.as_ref().unwrap().span(),
                                "Default methods in external trait specs are invalid"
                            ));
                        }

                        let method = self.generate_method_stub(trait_method);
                        struct_impl.items.push(syn::ImplItem::Method(method));
                    }
                    _ => unimplemented!("Unimplemented trait item for extern spec"),
                };
            }

            Ok(struct_impl)
        }

        /// Generates a "stub" implementation for a trait method
        fn generate_method_stub(&self, trait_method: &syn::TraitItemMethod) -> syn::ImplItemMethod {
            let mut trait_method_sig = trait_method.sig.clone();

            // Rewrite occurrences of associated types in signature to defined generics
            syn::visit_mut::visit_signature_mut(
                &mut AssociatedTypeRewriter::new(&self.assoc_types_to_generics_map),
                &mut trait_method_sig,
            );
            let trait_method_ident = &trait_method_sig.ident;

            // Rewrite "self" to "_self" in method attributes and method inputs
            let mut trait_method_attrs = trait_method.attrs.clone();
            trait_method_attrs
                .iter_mut()
                .for_each(|attr| attr.tokens = rewrite_self(attr.tokens.clone()));
            let trait_method_inputs =
                rewrite_method_inputs(&self.self_type_param_ident, &mut trait_method_sig.inputs);

            // Create the method signature
            let trait_ident = &self.item_trait.ident;
            let method_path: syn::ExprPath = parse_quote_spanned! {trait_method_ident.span()=>
                #trait_ident :: #trait_method_ident
            };

            // Create method
            return parse_quote_spanned! {trait_method.span()=>
                #[trusted]
                #[prusti::extern_spec]
                #(#trait_method_attrs)*
                #[allow(unused)]
                #trait_method_sig  {
                    #method_path ( #trait_method_inputs );
                    unimplemented!();
                }
            };
        }
    }

    fn get_associated_types(item_trait: &syn::ItemTrait) -> Vec<&syn::TraitItemType> {
        let mut result = Vec::new();
        for trait_item in item_trait.items.iter() {
            if let syn::TraitItem::Type(assoc_type) = trait_item {
                // TODO: How to handle associated types with defaults?
                result.push(assoc_type);
            }
        }
        result
    }

    /// Given a map from associated types to generic type params, this struct
    /// rewrites associated type paths to these generic params.
    ///
    /// # Example
    /// Given a mapping `AssocType1 -> T_AssocType1, AssocType2 -> T_AssocType2`,
    /// visiting a function
    /// ```
    /// fn foo(arg: Self::AssocType1) -> Self::AssocType2 { }
    /// ```
    /// results in
    /// ```
    /// fn foo(arg: T_AssocType1) -> T_AssocType2 { }
    /// ```
    ///
    struct AssociatedTypeRewriter<'a> {
        repl: &'a AssocTypesToGenericsMap<'a>,
    }

    impl<'a> AssociatedTypeRewriter<'a> {
        pub fn new(repl: &'a AssocTypesToGenericsMap<'a>) -> Self {
            AssociatedTypeRewriter { repl }
        }
    }

    impl<'a> syn::visit_mut::VisitMut for AssociatedTypeRewriter<'a> {
        fn visit_type_path_mut(&mut self, ty_path: &mut syn::TypePath) {
            let path = &ty_path.path;
            if path.segments.len() == 2
                && path.segments[0].ident.to_string() == "Self"
                && self.repl.contains_key(&path.segments[1].ident)
            {
                let replacement = self.repl.get(&path.segments[1].ident).unwrap();
                ty_path.path = parse_quote!(#replacement);
            }

            syn::visit_mut::visit_type_path_mut(self, ty_path);
        }
    }
}
