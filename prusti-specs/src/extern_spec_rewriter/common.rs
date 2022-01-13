use quote::{quote, quote_spanned, ToTokens};
use syn::spanned::Spanned;

/// Rewrites every occurence of "self" to "_self" in a token stream
pub fn rewrite_self(tokens: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
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
pub fn add_phantom_data_for_generic_params(item_struct: &mut syn::ItemStruct) {
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

pub fn rewrite_method_inputs<T: ToTokens>(
    item_ty: &T,
    method_inputs: &mut syn::punctuated::Punctuated<syn::FnArg, syn::Token![,]>,
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