extern crate proc_macro;

use proc_macro::TokenStream;
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
pub fn after_expiry(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

#[proc_macro_attribute]
pub fn after_expiry_if(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

#[proc_macro_attribute]
pub fn pure(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

#[proc_macro_attribute]
pub fn trusted(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

#[proc_macro]
pub fn body_invariant(_tokens: TokenStream) -> TokenStream {
    (quote! { () }).into()
}

#[proc_macro]
pub fn closure(tokens: TokenStream) -> TokenStream {
    prusti_specs::closure(tokens.into(), true).into()
}
