//! Process external specifications in Rust foreign modules marked with
//! the #[extern_spec] attribute.

use super::common::generate_extern_spec_foreign_function_stub;
use crate::{
    extract_prusti_attributes, generate_spec_and_assertions, specifications::untyped::AnyFnItem,
    ExternSpecKind,
};
use proc_macro2::TokenStream;
use quote::{quote, ToTokens};

pub fn rewrite_extern_spec(item_foreign_mod: &mut syn::ItemForeignMod) -> syn::Result<TokenStream> {
    let mut specs = vec![];
    for item in item_foreign_mod.items.iter_mut() {
        if let syn::ForeignItem::Fn(item_fn) = item {
            specs.extend(rewrite_fn(item_fn)?);
        }
        // eventually: handle specs for foreign variables
    }

    let mut res = TokenStream::new();
    res.extend(specs.iter().map(syn::Item::to_token_stream));
    res.extend(quote!(#item_foreign_mod));
    Ok(res)
}

fn rewrite_fn(item_fn: &mut syn::ForeignItemFn) -> Result<Vec<syn::Item>, syn::Error> {
    let stub_fn: syn::ForeignItemFn =
        generate_extern_spec_foreign_function_stub(item_fn, ExternSpecKind::Method);
    let mut stub_fn = AnyFnItem::ForeignFn(stub_fn);
    let prusti_attributes = extract_prusti_attributes(&mut stub_fn);
    let (spec_items, generated_attributes) =
        generate_spec_and_assertions(prusti_attributes, &stub_fn)?;
    stub_fn.attrs_mut().extend(generated_attributes);
    *item_fn = stub_fn.expect_foreign_item_fn();
    Ok(spec_items)
}
