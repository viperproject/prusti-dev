use proc_macro2::TokenStream;
use quote::ToTokens;

pub use super::common::{SpecType, SpecificationId};
pub use super::preparser::Arg;

/// An abstraction over all kinds of function items.
pub enum AnyFnItem {
    Fn(syn::ItemFn),
    TraitMethod(syn::TraitItemMethod),
    ImplMethod(syn::ImplItemMethod),
}

impl syn::parse::Parse for AnyFnItem {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        use syn::parse::discouraged::Speculative;
        let fork = input.fork();
        let item_fn = fork.parse();
        match item_fn {
            Ok(res) => {
                // We have an item Fn.
                input.advance_to(&fork);
                Ok(AnyFnItem::Fn(res))
            },
            Err(_) => {
                // It is not a valid ItemFn.
                let item_method = input.parse()?;
                Ok(AnyFnItem::TraitMethod(item_method))
            }
        }
    }
}

impl AnyFnItem {
    pub fn attrs_mut(&mut self) -> &mut Vec<syn::Attribute> {
        match self {
            AnyFnItem::Fn(item) => &mut item.attrs,
            AnyFnItem::TraitMethod(item) => &mut item.attrs,
            AnyFnItem::ImplMethod(item) => &mut item.attrs,
        }
    }

    pub fn sig(&self) -> &syn::Signature {
        match self {
            AnyFnItem::Fn(item) => &item.sig,
            AnyFnItem::TraitMethod(item) => &item.sig,
            AnyFnItem::ImplMethod(item) => &item.sig,
        }
    }

    pub fn block(&self) -> Option<&syn::Block> {
        match self {
            AnyFnItem::Fn(item) => Some(&item.block),
            AnyFnItem::ImplMethod(item) => Some(&item.block),
            AnyFnItem::TraitMethod(item) => item.default.as_ref(),
        }
    }
}

impl ToTokens for AnyFnItem {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            AnyFnItem::Fn(item) => item.to_tokens(tokens),
            AnyFnItem::TraitMethod(item) => item.to_tokens(tokens),
            AnyFnItem::ImplMethod(item) => item.to_tokens(tokens),
        }
    }
}
