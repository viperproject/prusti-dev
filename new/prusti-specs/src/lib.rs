#![feature(box_syntax)]
#![feature(box_patterns)]

use proc_macro2::TokenStream;
use quote::quote;

mod rewriter;
mod specifications;

macro_rules! handle_result {
    ($parse_result: expr) => {
        match $parse_result {
            Ok(data) => data,
            Err(err) => return err.to_compile_error(),
        };
    };
}

pub fn requires(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    let item: syn::ItemFn = handle_result!(syn::parse2(tokens));
    let mut rewriter = rewriter::AstRewriter::new();
    let assertion = handle_result!(rewriter.parse_assertion(attr));
    let spec_item = handle_result!(rewriter.generate_spec_item_fn("pre", assertion, &item));
    quote! {
        #spec_item
        #item
    }
}

pub fn ensures(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    let item: syn::ItemFn = handle_result!(syn::parse2(tokens));
    let mut rewriter = rewriter::AstRewriter::new();
    let assertion = handle_result!(rewriter.parse_assertion(attr));
    let spec_item = handle_result!(rewriter.generate_spec_item_fn("post", assertion, &item));
    quote! {
        #spec_item
        #item
    }
}

pub fn invariant(tokens: TokenStream) -> TokenStream {
    let mut rewriter = rewriter::AstRewriter::new();
    let invariant = handle_result!(rewriter.parse_assertion(tokens));
    let check = rewriter.generate_spec_loop(invariant);
    quote! {
        if false {
            #check
        }
    }
}
