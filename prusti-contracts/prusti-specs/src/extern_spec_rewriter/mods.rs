//! Process external specifications in Rust modules marked with the
//! #[extern_spec] attribute. Nested modules are processed recursively.
//! Specifications are collected from functions and function stubs.
//!
//! Modules are rewritten so that their name does not clash with the module
//! they are specifying.

use super::common::generate_extern_spec_function_stub;
use crate::{specifications::common::generate_mod_name, ExternSpecKind};
use proc_macro2::{Group, TokenStream, TokenTree};
use quote::{quote, ToTokens};
use syn::{parse_quote_spanned, spanned::Spanned};

pub fn rewrite_extern_spec(item_mod: &mut syn::ItemMod) -> syn::Result<TokenStream> {
    let path = syn::Path {
        leading_colon: None,
        segments: syn::punctuated::Punctuated::new(),
    };
    rewrite_mod(item_mod, &path)?;
    Ok(quote!(#item_mod))
}

fn rewrite_mod(item_mod: &mut syn::ItemMod, path: &syn::Path) -> syn::Result<()> {
    if item_mod.content.is_none() {
        return Ok(());
    }

    let mut path = path.clone();
    path.segments.push(syn::PathSegment {
        ident: item_mod.ident.clone(),
        arguments: syn::PathArguments::None,
    });
    item_mod.ident = syn::Ident::new(&generate_mod_name(&item_mod.ident), item_mod.span());

    for item in item_mod.content.as_mut().unwrap().1.iter_mut() {
        match item {
            syn::Item::Fn(item_fn) => {
                rewrite_fn(item_fn, &path);
            }
            syn::Item::Mod(inner_mod) => {
                rewrite_mod(inner_mod, &path)?;
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
                    rewrite_fn(item_fn, &path);
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
fn rewrite_fn(item_fn: &mut syn::ItemFn, path: &syn::Path) {
    let ident = &item_fn.sig.ident;
    let path_span = item_fn.sig.ident.span();
    let path = parse_quote_spanned!(path_span=> #path :: #ident);

    *item_fn = generate_extern_spec_function_stub(item_fn, &path, ExternSpecKind::Method);
}
