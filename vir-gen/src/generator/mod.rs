use crate::ast::*;
use proc_macro2::TokenStream;
use quote::{quote, ToTokens};

impl ToTokens for Declarations {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        for ir in &self.irs {
            tokens.extend(quote! {
                #ir
            });
        }
    }
}

impl ToTokens for CustomDeriveOptions {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let fields = &self.ignored_fields;
        tokens.extend(quote! {ignore=[#(#fields),*]})
    }
}

impl ToTokens for CustomDerive {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Self::New => tokens.extend(quote! {new}),
            Self::NewWithPos => tokens.extend(quote! {new_with_pos}),
            Self::PartialEq(options) => tokens.extend(quote! {PartialEq(#options)}),
            Self::Hash(options) => tokens.extend(quote! {Hash(#options)}),
            Self::Other(ident) => tokens.extend(quote! {#ident}),
        }
    }
}
