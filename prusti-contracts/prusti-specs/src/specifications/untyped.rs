use crate::common::HasSignature;
use proc_macro2::TokenStream;
use quote::ToTokens;
use syn::Signature;

pub use super::{
    common::{SpecType, SpecificationId},
    preparser::Arg,
};

/// An abstraction over all kinds of function items.
#[derive(Debug, PartialEq, Eq)]
pub enum AnyFnItem {
    Fn(syn::ItemFn),
    TraitMethod(syn::TraitItemMethod),
    ImplMethod(syn::ImplItemMethod),
    ForeignFn(syn::ForeignItemFn),
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
            }
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
            AnyFnItem::ForeignFn(item) => &mut item.attrs,
        }
    }

    pub fn block(&self) -> Option<&syn::Block> {
        match self {
            AnyFnItem::Fn(item) => Some(&item.block),
            AnyFnItem::ImplMethod(item) => Some(&item.block),
            AnyFnItem::TraitMethod(item) => item.default.as_ref(),
            AnyFnItem::ForeignFn(_) => None,
        }
    }

    pub fn vis(&self) -> Option<&syn::Visibility> {
        match self {
            AnyFnItem::Fn(item) => Some(&item.vis),
            AnyFnItem::ImplMethod(item) => Some(&item.vis),
            AnyFnItem::TraitMethod(_) => None,
            AnyFnItem::ForeignFn(item) => Some(&item.vis),
        }
    }

    pub fn expect_impl_item(self) -> syn::ImplItemMethod {
        match self {
            AnyFnItem::ImplMethod(i) => i,
            _ => unreachable!(),
        }
    }

    pub fn expect_foreign_item_fn(self) -> syn::ForeignItemFn {
        match self {
            AnyFnItem::ForeignFn(f) => f,
            _ => unreachable!(),
        }
    }
}

impl HasSignature for AnyFnItem {
    fn sig(&self) -> &Signature {
        match self {
            Self::Fn(item) => item.sig(),
            Self::ImplMethod(item) => item.sig(),
            Self::TraitMethod(item) => item.sig(),
            Self::ForeignFn(item) => item.sig(),
        }
    }

    fn sig_mut(&mut self) -> &mut Signature {
        match self {
            Self::Fn(item) => item.sig_mut(),
            Self::ImplMethod(item) => item.sig_mut(),
            Self::TraitMethod(item) => item.sig_mut(),
            Self::ForeignFn(item) => item.sig_mut(),
        }
    }
}

impl ToTokens for AnyFnItem {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            AnyFnItem::Fn(item) => item.to_tokens(tokens),
            AnyFnItem::TraitMethod(item) => item.to_tokens(tokens),
            AnyFnItem::ImplMethod(item) => item.to_tokens(tokens),
            AnyFnItem::ForeignFn(item) => item.to_tokens(tokens),
        }
    }
}
