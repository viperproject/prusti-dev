use proc_macro2::TokenStream;
use quote::quote;

pub fn requires(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

pub fn ensures(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

pub fn invariant(_tokens: TokenStream) -> TokenStream {
    quote!(if (false) {})
}
