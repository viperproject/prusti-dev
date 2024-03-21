#![feature(box_patterns)]

use proc_macro::TokenStream;

mod hash;
mod reify;
pub(crate) mod reify_kind;
mod serde;

#[proc_macro_derive(VirHash)]
pub fn derive_hash(input: TokenStream) -> TokenStream {
    hash::derive_hash(input)
}

#[proc_macro_derive(VirReify, attributes(vir))]
pub fn derive_reify(input: TokenStream) -> TokenStream {
    reify::derive_reify(input)
}

#[proc_macro_derive(VirSerde, attributes(vir))]
pub fn derive_serde(input: TokenStream) -> TokenStream {
    serde::derive_serde(input)
}
