extern crate proc_macro;

use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, Item};

#[proc_macro_attribute]
pub fn return_as_is(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    // item
    let item = parse_macro_input!(tokens as Item);

    // Build the output, possibly using quasi-quotation
    let expanded = quote! {
        fn test(x: u32) {}
        #item
    };

    // Hand the output tokens back to the compiler
    TokenStream::from(expanded)
}