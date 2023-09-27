// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(proc_macro_quote)]

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::{token::Paren, ItemFn, ReturnType, Type, TypeParen};

// Using `tracing::instrument` without this crate (from the vanilla tracing crate)
// causes RA to not pick up the return type properly atm - it colours wrong and
// appears like a local variable on hover. Somehow this is fixed by wrapping the
// return type in brackets (i.e. `-> TokenStream` to `-> (TokenStream)`) and so we
// do that here.
#[proc_macro_attribute]
pub fn instrument(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    let (attr, tokens): (TokenStream2, TokenStream2) = (attr.into(), tokens.into());
    if let Ok(mut item) = syn::parse2::<ItemFn>(tokens.clone()) {
        if let ReturnType::Type(a, ty) = item.sig.output {
            let new_ty = Type::Paren(TypeParen {
                paren_token: Paren::default(),
                elem: ty,
            });
            item.sig.output = ReturnType::Type(a, Box::new(new_ty));
        }
        quote! {
            #[tracing::tracing_instrument(#attr)]
            #item
        }
        .into()
    } else {
        quote! {
            #[tracing::tracing_instrument(#attr)]
            #tokens
        }
        .into()
    }
}
