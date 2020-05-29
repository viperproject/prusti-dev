extern crate proc_macro;

use proc_macro::TokenStream;

#[proc_macro_attribute]
pub fn expand_specs(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    prusti_specs::expand_specs(attr.into(), tokens.into()).into()
}
