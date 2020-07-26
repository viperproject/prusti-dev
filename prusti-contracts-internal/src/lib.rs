extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro_hack::proc_macro_hack;

#[proc_macro_attribute]
pub fn requires(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    prusti_specs::requires(attr.into(), tokens.into()).into()
}

#[proc_macro_attribute]
pub fn ensures(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    prusti_specs::ensures(attr.into(), tokens.into()).into()
}

#[proc_macro_attribute]
pub fn pure(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    prusti_specs::pure(attr.into(), tokens.into()).into()
}

#[proc_macro_hack]
pub fn invariant(tokens: TokenStream) -> TokenStream {
    prusti_specs::invariant(tokens.into()).into()
}
