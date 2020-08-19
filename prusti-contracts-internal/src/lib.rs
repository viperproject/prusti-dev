extern crate proc_macro;

use proc_macro::TokenStream;

#[proc_macro_attribute]
pub fn requires(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    prusti_specs::requires(attr.into(), tokens.into()).into()
}

#[proc_macro_attribute]
pub fn ensures(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    prusti_specs::ensures(attr.into(), tokens.into()).into()
}

#[proc_macro_attribute]
pub fn after_expiry(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    prusti_specs::after_expiry(attr.into(), tokens.into()).into()
}

#[proc_macro_attribute]
pub fn after_expiry_if(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    prusti_specs::after_expiry_if(attr.into(), tokens.into()).into()
}

#[proc_macro_attribute]
pub fn pure(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    prusti_specs::pure(attr.into(), tokens.into()).into()
}

#[proc_macro_attribute]
pub fn trusted(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    prusti_specs::trusted(attr.into(), tokens.into()).into()
}

#[proc_macro]
pub fn body_invariant(tokens: TokenStream) -> TokenStream {
    prusti_specs::body_invariant(tokens.into()).into()
}

#[proc_macro]
pub fn closure(tokens: TokenStream) -> TokenStream {
    prusti_specs::closure(tokens.into(), false).into()
}
