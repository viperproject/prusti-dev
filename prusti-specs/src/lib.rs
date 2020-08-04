#![feature(box_syntax)]
#![feature(box_patterns)]

use proc_macro2::TokenStream;
use quote::quote;
use syn::spanned::Spanned;

use specifications::untyped;

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

/// Check if the given expression is identifier `result`.
fn check_is_result(reference: &Option<untyped::Expression>) -> syn::Result<()> {
    if let Some(untyped::Expression { expr, ..}) = reference {
        if let syn::Expr::Path(syn::ExprPath { qself: None, path, ..}) = expr {
            if path.is_ident("result") {
                return Ok(());
            }
        }
        Err(syn::Error::new(
            expr.span(),
            "currently only `result` is supported".to_string(),
        ))
    } else {
        Ok(())
    }
}

pub fn after_expiry(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    let item: syn::ItemFn = handle_result!(syn::parse2(tokens));
    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id_rhs = rewriter.generate_spec_id();
    let spec_id_rhs_str = format!(":{}", spec_id_rhs);
    let pledge = handle_result!(rewriter.parse_pledge(None, spec_id_rhs, attr));
    handle_result!(check_is_result(&pledge.reference));
    assert!(pledge.lhs.is_none(), "after_expiry with lhs?");
    let spec_item_rhs =
        handle_result!(rewriter.generate_spec_item_fn(rewriter::SpecItemType::Postcondition, spec_id_rhs, pledge.rhs, &item));
    quote! {
        #spec_item_rhs
        #[prusti::pledge_spec_id_ref = #spec_id_rhs_str]
        #item
    }
}

pub fn after_expiry_if(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    let item: syn::ItemFn = handle_result!(syn::parse2(tokens));
    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id_lhs = rewriter.generate_spec_id();
    let spec_id_rhs = rewriter.generate_spec_id();
    let spec_id_str = format!("{}:{}", spec_id_lhs, spec_id_rhs);
    let pledge = handle_result!(rewriter.parse_pledge(Some(spec_id_lhs), spec_id_rhs, attr));
    handle_result!(check_is_result(&pledge.reference));
    let spec_item_lhs =
        handle_result!(rewriter.generate_spec_item_fn(rewriter::SpecItemType::Postcondition, spec_id_lhs, pledge.lhs.unwrap(), &item));
    let spec_item_rhs =
        handle_result!(rewriter.generate_spec_item_fn(rewriter::SpecItemType::Postcondition, spec_id_rhs, pledge.rhs, &item));
    quote! {
        #spec_item_lhs
        #spec_item_rhs
        #[prusti::pledge_spec_id_ref = #spec_id_str]
        #item
    }
}

pub fn pure(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    quote! {
        #[prusti::pure]
        #tokens
    }
}

pub fn trusted(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    quote! {
        #[prusti::trusted]
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
