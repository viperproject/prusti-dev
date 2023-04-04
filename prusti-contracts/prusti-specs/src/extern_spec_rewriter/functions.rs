//! Process external specifications on free functions.
//! In practice, these will be combined with a module argument to extern_spec
//! e.g. `#[extern_spec(core::mem)] fn swap`

use super::common::generate_extern_spec_function_stub;
use crate::ExternSpecKind;
use proc_macro2::{Group, TokenStream, TokenTree};
use quote::{quote, ToTokens};
use syn::{parse_quote_spanned, spanned::Spanned};

pub fn rewrite_stub(
    stub_tokens: &TokenStream,
    path: &syn::Path,
    is_unsafe: bool,
) -> syn::Result<TokenStream> {
    // Transforms function stubs (functions with a `;` after the
    // signature instead of the body) into functions, then
    // processes them.
    let mut new_tokens = TokenStream::new();
    for mut token in stub_tokens.clone().into_iter() {
        if let TokenTree::Punct(punct) = &mut token {
            if punct.as_char() == ';' {
                new_tokens.extend(
                    Group::new(proc_macro2::Delimiter::Brace, TokenStream::new()).to_token_stream(),
                );
                continue;
            }
        }
        new_tokens.extend(token.to_token_stream());
    }
    let res: Result<syn::Item, _> = syn::parse2(new_tokens);
    if res.is_err() {
        return Err(syn::Error::new(
            stub_tokens.span(),
            "invalid function signature",
        ));
    }

    let mut item = res.unwrap();
    if let syn::Item::Fn(item_fn) = &mut item {
        Ok(rewrite_fn(item_fn, path, is_unsafe))
    } else {
        Ok(quote!(#item))
    }
}

/// Rewrite a specification function to a call to the specified function.
/// The result of this rewriting is then parsed in `ExternSpecResolver`.
pub fn rewrite_fn(item_fn: &syn::ItemFn, path: &syn::Path, is_unsafe: bool) -> TokenStream {
    let ident = &item_fn.sig.ident;
    let path_span = item_fn.sig.ident.span();
    let path = parse_quote_spanned!(path_span=> #path :: #ident);

    generate_extern_spec_function_stub(item_fn, &path, ExternSpecKind::Method, true, is_unsafe)
}
