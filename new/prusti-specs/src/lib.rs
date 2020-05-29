use proc_macro2::TokenStream;
use quote::quote;
use syn::File;

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
    let krate: File = match syn::parse2(tokens) {
        Ok(data) => data,
        Err(err) => return err.to_compile_error(),
    };
    let expanded = quote! {
        #krate
    };
    // Hand the output tokens back to the compiler
    TokenStream::from(expanded)
}
