extern crate proc_macro;

use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, File};

#[proc_macro_attribute]
pub fn expand_specs(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    let krate = parse_macro_input!(tokens as File);
    let expanded = quote! {
        #krate
    };
    // Hand the output tokens back to the compiler
    TokenStream::from(expanded)
}
