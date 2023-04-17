//! Process external specifications in Rust modules marked with the
//! #[extern_spec] attribute. Nested modules are processed recursively.
//! Specifications are collected from functions and function stubs.
//!
//! Modules are rewritten so that their name does not clash with the module
//! they are specifying.

use super::{
    common::check_is_stub,
    functions::{rewrite_fn, rewrite_stub},
};
use proc_macro2::TokenStream;
use syn::spanned::Spanned;

pub fn rewrite_mod(item_mod: &syn::ItemMod, mut path: syn::Path) -> syn::Result<TokenStream> {
    path.segments.push(syn::PathSegment {
        ident: item_mod.ident.clone(),
        arguments: syn::PathArguments::None,
    });

    let mut rewritten_fns = TokenStream::new();
    for item in item_mod.content.as_ref().iter().flat_map(|c| &c.1) {
        match item {
            syn::Item::Fn(ref item_fn) => {
                check_is_stub(&item_fn.block)?;
                rewritten_fns.extend(rewrite_fn(item_fn, &path, false));
            }
            syn::Item::Mod(ref inner_mod) => rewritten_fns.extend(rewrite_mod(inner_mod, path.clone())?),
            syn::Item::Verbatim(ref tokens) => rewritten_fns.extend(rewrite_stub(tokens, &path, false)?),
            syn::Item::Use(_) => rewritten_fns.extend(syn::Error::new(
                item.span(),
                "`use` statements have no effect in #[extern_spec] modules; module contents share the outer scope.",
            ).to_compile_error()),
            _ => return Err(syn::Error::new(item.span(), "unexpected item")),
        }
    }

    Ok(rewritten_fns)
}
