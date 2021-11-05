use crate::specifications::common::NameGenerator;
use super::parse_quote_spanned;
use proc_macro2::{TokenStream, TokenTree, Group};
use quote::{quote, quote_spanned, ToTokens};
use syn::ImplItemMethod;
use syn::spanned::Spanned;
use crate::span_overrider::SpanOverrider;

/// Process external specifications in Rust modules marked with the
/// #[extern_spec] attribute. Nested modules are processed recursively.
/// Specifications are collected from functions and function stubs.
///
/// Modules are rewritten so that their name does not clash with the module
/// they are specifying.
pub fn rewrite_mod(item_mod: &mut syn::ItemMod, path: &mut syn::Path) -> syn::Result<()> {
    if item_mod.content.is_none() {
        return Ok(())
    }

    path.segments.push(syn::PathSegment { ident: item_mod.ident.clone(), arguments: syn::PathArguments::None });
    let name_generator = NameGenerator::new();
    item_mod.ident = syn::Ident::new(&name_generator.generate_mod_name(&item_mod.ident),
                                    item_mod.span());

    for item in item_mod.content.as_mut().unwrap().1.iter_mut() {
        match item {
            syn::Item::Fn(item_fn) => {
                rewrite_fn(item_fn, path);
            },
            syn::Item::Mod(inner_mod) => {
                rewrite_mod(inner_mod, path)?;
            },
            syn::Item::Verbatim(tokens) => {
                // Transforms function stubs (functions with a `;` after the
                // signature instead of the body) into functions, then
                // processes them.
                let mut new_tokens = TokenStream::new();
                for mut token in tokens.clone().into_iter() {
                    if let TokenTree::Punct(punct) = &mut token {
                        if punct.as_char() == ';' {
                            new_tokens.extend(Group::new(proc_macro2::Delimiter::Brace, TokenStream::new()).to_token_stream());
                            continue;
                        }
                    }
                    new_tokens.extend(token.to_token_stream());
                }
                let res: Result<syn::Item, _> = syn::parse2(new_tokens);
                if res.is_err() {
                    return Err(syn::Error::new(
                        item.span(),
                        "invalid function signature",
                    ))
                }

                let mut item = res.unwrap();
                if let syn::Item::Fn(item_fn) = &mut item {
                    rewrite_fn(item_fn, path);
                }
                *tokens = quote!(#item)
            }
            syn::Item::Use(_) => {}
            _ => return Err(syn::Error::new(
                item.span(),
                "unexpected item",
            ))
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

    item_fn.attrs.push(parse_quote_spanned!(item_fn_span=> #[prusti::extern_spec]));
    item_fn.attrs.push(parse_quote_spanned!(item_fn_span=> #[trusted]));
}

/// Rewrite all methods in an impl block to calls to the specified methods.
/// The result of this rewriting is then parsed in `ExternSpecResolver`.
pub fn rewrite_impl(
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

                let args = rewrite_method_inputs(item_ty, method);
                let ident = &method.sig.ident;

                method.attrs.push(parse_quote_spanned!(item_span=> #[prusti::extern_spec]));
                method.attrs.push(parse_quote_spanned!(item_span=> #[trusted]));

                let mut method_path: syn::ExprPath = parse_quote_spanned! {ident.span()=>
                    #item_ty :: #ident
                };

                // Fix the span
                syn::visit_mut::visit_expr_path_mut(
                    &mut SpanOverrider::new(ident.span()),
                    &mut method_path
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

fn rewrite_self(tokens: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let mut new_tokens = proc_macro2::TokenStream::new();
    for token in tokens.into_iter() {
        match token {
            proc_macro2::TokenTree::Group(group) => {
                let new_group = proc_macro2::Group::new(group.delimiter(),
                                                        rewrite_self(group.stream()));
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

fn rewrite_method_inputs(item_ty: &syn::Type, method: &mut ImplItemMethod) ->
    syn::punctuated::Punctuated<syn::Expr, syn::token::Comma> {
    let mut args: syn::punctuated::Punctuated<syn::Expr, syn::token::Comma> =
        syn::punctuated::Punctuated::new();

    for input in method.sig.inputs.iter_mut() {
        let input_span = input.span();
        match input {
            syn::FnArg::Receiver(receiver) => {
                let and = if receiver.reference.is_some() {
                    // TODO: do lifetimes need to be specified here?
                    quote_spanned! {input_span=> &}
                } else {
                    quote! { }
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
    };
    args
}

/// Generate an empty struct to be able to define impl blocks (in
/// `rewrite_impl`) on it for its specification functions.
pub fn generate_new_struct(item: &syn::ItemImpl) -> syn::Result<syn::ItemStruct> {
    let name_generator = NameGenerator::new();
    let struct_name = match name_generator.generate_struct_name(item) {
        Ok(name) => name,
        Err(msg) => return Err(syn::Error::new(
            item.span(),
            msg,
        ))
    };
    let struct_ident = syn::Ident::new(&struct_name,
                                       item.span());

    let mut new_struct: syn::ItemStruct = parse_quote_spanned! {item.span()=>
        #[allow(non_camel_case_types)] struct #struct_ident {}
    };

    new_struct.generics = item.generics.clone();
    let generics = &new_struct.generics;

    let mut fields = vec![];

    // Add `PhantomData` markers for each type parameter to silence errors
    // about unused type parameters.
    for param in generics.params.iter() {
        let field: ParsableUnnamedField = match param {
            syn::GenericParam::Type(tp) => {
                let ident = tp.ident.clone();
                syn::parse_quote!{ ::core::marker::PhantomData<#ident> }
            }
            syn::GenericParam::Lifetime(ld) => {
                let ident = ld.lifetime.clone();
                syn::parse_quote!{ &#ident ::core::marker::PhantomData<()> }
            }
            syn::GenericParam::Const(_cp) => continue,
        };
        // Unwrap the `ParsableUnnamedField` and push. See below.
        fields.push(field.0);
    }

    new_struct.fields = syn::Fields::Unnamed( syn::parse_quote!{ ( #(#fields),* ) } );
    Ok(new_struct)
}

/// The `syn::Field` doesn't implement `syn::parse::Parse` directly since it can do
/// both `parse_unnamed` and `parse_named`. This is a wrapper to tell `parse_quote`
/// to use `parse_unnamed` when parsing. https://github.com/dtolnay/syn/issues/651
struct ParsableUnnamedField(syn::Field);
impl syn::parse::Parse for ParsableUnnamedField {
    fn parse(input: syn::parse::ParseStream<'_>) -> syn::parse::Result<Self> {
        Ok(ParsableUnnamedField( syn::Field::parse_unnamed(input)? ))
    }
}

/// We take the Generics (parameters) defined with the `#[extern_spec] impl<...>` (the `<...>`)
/// but then need to pass those as arguments: `SomeStruct<...>`. This function translates from
/// the syntax of one to the other; e.g. `<T: Bound, 'l: Bound, const C: usize>` -> `<T, 'l, C>`
pub fn rewrite_generics(gens: &syn::Generics) -> syn::AngleBracketedGenericArguments {
    let args: Vec<syn::GenericArgument> = gens.params.clone().iter().map(|gp| {
        let ts = match gp {
            syn::GenericParam::Type(syn::TypeParam { ident, .. }) |
            syn::GenericParam::Const(syn::ConstParam { ident, .. }) => ident.into_token_stream(),
            syn::GenericParam::Lifetime(ld) => ld.lifetime.clone().into_token_stream(),
        };
        syn::parse2::<syn::GenericArgument>(ts).unwrap()
    }).collect();
    syn::parse_quote!{ < #(#args),* > }
}
