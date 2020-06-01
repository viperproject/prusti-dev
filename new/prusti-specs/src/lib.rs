use proc_macro2::TokenStream;
use quote::quote;
use syn::{visit_mut::VisitMut, File};

mod rewriter;
mod specifications;

pub fn requires(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    quote! {
        #[prusti::requires(#attr)]
        #tokens
    }
}

pub fn ensures(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    quote! {
        #[prusti::ensures(#attr)]
        #tokens
    }
}

pub fn invariant(_tokens: TokenStream) -> TokenStream {
    quote!(if (false) {})
}

pub fn expand_specs(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    assert!(attr.is_empty());
    let mut krate: File = match syn::parse2(tokens) {
        Ok(data) => data,
        Err(err) => return err.to_compile_error(),
    };
    let mut rewriter = rewriter::AstRewriter::new();
    rewriter.visit_file_mut(&mut krate);
    let errors = rewriter.error_tokens();
    quote! {
        #krate

        #errors
    }
}
