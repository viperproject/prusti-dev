// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::ast::*;
use proc_macro2::TokenStream;
use quote::{quote, ToTokens};

impl ToTokens for CustomDeriveOptions {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let trait_type = &self.trait_type;
        let fields = &self.ignored_fields;
        tokens.extend(quote! {trait_type=#trait_type,ignore=[#(#fields),*]})
    }
}

impl ToTokens for CustomDerive {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Self::New => tokens.extend(quote! {new}),
            Self::NewWithPos => tokens.extend(quote! {new_with_pos}),
            Self::PartialEq(options) => tokens.extend(quote! {PartialEq(#options)}),
            Self::Ord(options) => tokens.extend(quote! {Ord(#options)}),
            Self::Hash(options) => tokens.extend(quote! {Hash(#options)}),
            Self::Other(ident) => tokens.extend(quote! {#ident}),
        }
    }
}
