#![no_std]
extern crate proc_macro;

use proc_macro::TokenStream;

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
pub fn assert_on_expiry(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
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
    TokenStream::new()
}

#[proc_macro_attribute]
pub fn refine_trait_spec(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

#[proc_macro_attribute]
pub fn extern_spec(_attr: TokenStream, _tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[proc_macro]
pub fn predicate(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[proc_macro_attribute]
pub fn model(_attr: TokenStream, _tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[proc_macro_attribute]
pub fn ghost_constraint(_attr: TokenStream, _tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[proc_macro]
pub fn ghost(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}
