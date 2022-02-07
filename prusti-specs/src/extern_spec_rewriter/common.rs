use proc_macro2::{TokenStream, TokenTree};
use quote::{quote, quote_spanned, ToTokens};
use syn::spanned::Spanned;
use std::collections::HashMap;

/// Rewrites every occurence of "self" to "_self" in a token stream
pub fn rewrite_self(tokens: TokenStream) -> TokenStream {
    TokenStream::from_iter(tokens
        .into_iter()
        .map(|token| match token {
            TokenTree::Group(group) => {
                let new_group =
                    proc_macro2::Group::new(group.delimiter(), rewrite_self(group.stream()));
                new_group.to_token_stream()
            }
            TokenTree::Ident(mut ident) => {
                if ident == "self" {
                    ident = proc_macro2::Ident::new("_self", ident.span());
                }
                ident.into_token_stream()
            }
            _ => token.into_token_stream(),
        }))
}

/// Add `PhantomData` markers for each type parameter to silence errors
/// about unused type parameters.
///
/// Given
/// ```text
/// struct Foo<A,B> {
/// }
/// ```
/// Result
/// ```text
/// struct Foo<A,B> {
///     ::core::marker::PhantomData<A>,
///     ::core::marker::PhantomData<B>
/// }
/// ```
pub fn add_phantom_data_for_generic_params(item_struct: &mut syn::ItemStruct) {
    let fields = item_struct.generics.params.iter()
        .flat_map(|param| match param {
            syn::GenericParam::Type(tp) => {
                let ident = tp.ident.clone();
                Some(quote!(::core::marker::PhantomData<#ident>))
            }
            syn::GenericParam::Lifetime(ld) => {
                let ident = ld.lifetime.clone();
                Some(quote!(&#ident ::core::marker::PhantomData<()>))
            }
            syn::GenericParam::Const(_cp) => None,
        });

    item_struct.fields = syn::Fields::Unnamed(syn::parse_quote! { ( #(#fields),* ) });
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

pub fn rewrite_method_inputs<T: ToTokens>(
    item_ty: &T,
    method_inputs: &mut syn::punctuated::Punctuated<syn::FnArg, syn::Token![,]>,
) -> syn::punctuated::Punctuated<syn::Expr, syn::Token![,]> {
    let mut args: syn::punctuated::Punctuated<syn::Expr, syn::Token![,]> =
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
        args.push_punct(<syn::Token![,]>::default());
    }
    args
}

/// Given a map from associated types to anything tokenizable, this struct
/// rewrites associated type paths to these tokens.
///
/// # Example
/// Given a mapping from associated types to generic type params
/// `[AssocType1 -> T_AssocType1, AssocType2 -> T_AssocType2]`,
/// visiting a function
/// ```
/// fn foo(arg: Self::AssocType1) -> Self::AssocType2 { }
/// ```
/// results in
/// ```
/// fn foo(arg: T_AssocType1) -> T_AssocType2 { }
/// ```
///
pub struct AssociatedTypeRewriter<'a, R: ToTokens> {
    repl: &'a HashMap<&'a syn::Ident, R>,
}

impl<'a, R: ToTokens> AssociatedTypeRewriter<'a, R> {
    pub fn new(repl: &'a HashMap<&'a syn::Ident, R>) -> Self {
        AssociatedTypeRewriter { repl }
    }

    pub fn rewrite_method_sig(&mut self, signature: &mut syn::Signature) {
        syn::visit_mut::visit_signature_mut(self,signature);
    }
}

impl<'a, R: ToTokens> syn::visit_mut::VisitMut for AssociatedTypeRewriter<'a, R> {
    fn visit_type_path_mut(&mut self, ty_path: &mut syn::TypePath) {
        let path = &ty_path.path;
        if path.segments.len() == 2
            && path.segments[0].ident == "Self"
            && self.repl.contains_key(&path.segments[1].ident)
        {
            let replacement = self.repl.get(&path.segments[1].ident).unwrap();
            ty_path.path = syn::parse_quote!(#replacement);
        }

        syn::visit_mut::visit_type_path_mut(self, ty_path);
    }
}