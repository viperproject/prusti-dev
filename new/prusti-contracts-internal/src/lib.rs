extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use syn::{parse_macro_input, Ident, Item};

#[proc_macro_attribute]
pub fn expand_specs(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    // item
    let item = parse_macro_input!(tokens as Item);

    // Build the output, possibly using quasi-quotation
    let item_name = match &item {
        Item::Mod(item_mod) => &item_mod.ident,
        Item::Fn(item_fn) => &item_fn.sig.ident,
        x => unimplemented!("item: {:?}", x),
    };
    let new_item_name = Ident::new(&format!("test_{}", item_name), Span::call_site());
    let expanded = quote! {
        fn #new_item_name(x: u32) -> u32 {
            let x = 4u32;
            let y = x + 4u32;
            y
        }
        #item
    };

    // Hand the output tokens back to the compiler
    TokenStream::from(expanded)
}
