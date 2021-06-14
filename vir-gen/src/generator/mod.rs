use crate::ast::*;
use proc_macro2::TokenStream;
use quote::{quote, ToTokens};

impl ToTokens for Declarations {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        for ir in &self.irs {
            tokens.extend(quote! {
                #ir
            });
        }
    }
}
