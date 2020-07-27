extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro_hack::proc_macro_hack;
use quote::quote;

#[proc_macro_attribute]
pub fn requires(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

#[proc_macro_attribute]
pub fn ensures(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

#[proc_macro_attribute]
pub fn pure(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

#[proc_macro_hack]
pub fn invariant(_tokens: TokenStream) -> TokenStream {
    (quote! { () }).into()
}
