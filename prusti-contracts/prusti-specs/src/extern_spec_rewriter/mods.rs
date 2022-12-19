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
use crate::specifications::common::generate_mod_name;
use proc_macro2::TokenStream;
use quote::quote;
use syn::spanned::Spanned;

pub fn rewrite_extern_spec(
    item_mod: &mut syn::ItemMod,
    path: syn::Path,
) -> syn::Result<TokenStream> {
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
                check_is_stub(&item_fn.block)?;
                rewrite_fn(item_fn, &path);
            }
            syn::Item::Mod(inner_mod) => {
                rewrite_mod(inner_mod, &path)?;
            }
            syn::Item::Verbatim(tokens) => {
                rewrite_stub(tokens, &path)?;
            }
            syn::Item::Use(_) => {}
            _ => return Err(syn::Error::new(item.span(), "unexpected item")),
        }
    }
    Ok(())
}
