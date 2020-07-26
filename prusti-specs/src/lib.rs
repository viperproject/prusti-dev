#![feature(box_syntax)]
#![feature(box_patterns)]

use proc_macro2::TokenStream;
use quote::quote;

mod rewriter;
pub mod specifications;

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
    let spec_id = rewriter.generate_spec_id();
    let spec_id_str = spec_id.to_string();
    let assertion = handle_result!(rewriter.parse_assertion(spec_id, attr));
    let spec_item =
        handle_result!(rewriter.generate_spec_item_fn(rewriter::SpecItemType::Precondition, spec_id, assertion, &item));
    quote! {
        #spec_item
        #[prusti::pre_spec_id_ref = #spec_id_str]
        #item
    }
}

pub fn ensures(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    let item: syn::ItemFn = handle_result!(syn::parse2(tokens));
    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id = rewriter.generate_spec_id();
    let spec_id_str = spec_id.to_string();
    let assertion = handle_result!(rewriter.parse_assertion(spec_id, attr));
    let spec_item =
        handle_result!(rewriter.generate_spec_item_fn(rewriter::SpecItemType::Postcondition, spec_id, assertion, &item));
    quote! {
        #spec_item
        #[prusti::post_spec_id_ref = #spec_id_str]
        #item
    }
}

pub fn pure(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    quote! {
        #[prusti::pure]
        #tokens
    }
}

pub fn invariant(tokens: TokenStream) -> TokenStream {
    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id = rewriter.generate_spec_id();
    let invariant = handle_result!(rewriter.parse_assertion(spec_id, tokens));
    let check = rewriter.generate_spec_loop(spec_id, invariant);
    quote! {
        if false {
            #check
        }
    }
}
