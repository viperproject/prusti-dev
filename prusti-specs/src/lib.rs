#![feature(box_syntax)]
#![feature(box_patterns)]

use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::spanned::Spanned;

use specifications::untyped;
use parse_closure_macro::ClosureWithSpec;

mod rewriter;
mod parse_closure_macro;
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

pub fn body_invariant(tokens: TokenStream) -> TokenStream {
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

/// Unlike the functions above, which are only called from
/// prusti-contracts-internal, this function also needs to be called
/// from prusti-contracts-impl, because we still need to parse the
/// macro in order to replace it with the closure definition.
/// Therefore, there is an extra parameter drop_spec here which tells
/// the function whether to keep the specification (for -internal) or
/// drop it (for -impl).
pub fn closure(tokens: TokenStream, drop_spec: bool) -> TokenStream {
    let cl_spec = syn::parse::<ClosureWithSpec>(tokens.into());
    if let Err(err) = cl_spec {
        return err.to_compile_error();
    }
    let cl_spec = cl_spec.unwrap();

    if drop_spec {
        cl_spec.cl.into_token_stream()
    } else {
        let mut rewriter = rewriter::AstRewriter::new();

        let mut preconds: Vec<(untyped::SpecificationId,untyped::Assertion)> = Vec::new();
        let mut postconds: Vec<(untyped::SpecificationId,untyped::Assertion)> = Vec::new();

        let mut cl_annotations = TokenStream::new();

        for r in cl_spec.pres {
            let spec_id = rewriter.generate_spec_id();
            let precond = handle_result!(rewriter.parse_assertion(spec_id, r.to_token_stream()));
            preconds.push((spec_id, precond));
            let spec_id_str = spec_id.to_string();
            cl_annotations.extend(quote! {
                #[prusti::pre_spec_id_ref = #spec_id_str]
            });
        }

        for e in cl_spec.posts {
            let spec_id = rewriter.generate_spec_id();
            let postcond = handle_result!(rewriter.parse_assertion(spec_id, e.to_token_stream()));
            postconds.push((spec_id, postcond));
            let spec_id_str = spec_id.to_string();
            cl_annotations.extend(quote! {
                #[prusti::post_spec_id_ref = #spec_id_str]
            });
        }

        let syn::ExprClosure { attrs, asyncness, movability, capture, or1_token,
                               inputs, or2_token, output, body } = cl_spec.cl;

        let output_type: syn::Type = match output {
            syn::ReturnType::Default => {
                return syn::Error::new(output.span(), "closure must specify return type")
                    .to_compile_error();
            }
            syn::ReturnType::Type(_, ref ty) => (**ty).clone()
        };

        let (spec_toks_pre, spec_toks_post) = rewriter.generate_cl_spec(
            inputs.clone(), output_type, preconds, postconds);

        let mut attrs_ts = TokenStream::new();
        for a in attrs {
            attrs_ts.extend(a.into_token_stream());
        }

        quote! {
            {
                #cl_annotations #attrs_ts
                #asyncness #movability #capture
                #or1_token #inputs #or2_token #output
                {
                    if false {
                        #spec_toks_pre
                    }
                    let result = #body ;
                    if false {
                        #spec_toks_post
                    }
                    result
                }
            }
        }
    }
}
