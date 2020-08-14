#![feature(box_syntax)]
#![feature(box_patterns)]

use proc_macro2::{TokenStream, TokenTree, TokenTree::{Ident, Group, Punct}};
use quote::{quote, ToTokens};
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

/** Unlike the functions above, which are only called from
 *  prusti-contracts-internal, this function also needs to be called
 *  from prusti-contracts-impl, because we still need to parse the
 *  macro in order to replace it with the closure definition.
 *  Therefore, there is an extra parameter drop_spec here which tells
 *  the function whether to keep the specification (for -internal) or
 *  drop it (for -impl).
 */
pub fn closure(tokens: TokenStream, drop_spec: bool) -> TokenStream {
    let mut requires: Vec<TokenTree> = vec! [];
    let mut ensures: Vec<TokenTree> = vec! [];
    let mut cl: Option<syn::ExprClosure> = None;

    let mut iter = tokens.clone ().into_iter();

    while let Some(tok) = iter.next() {
        match tok {
            Ident(id) => {
                let total_span;

                if id.to_string() == "requires" {
                    match iter.next() {
                        Some(Group(g)) => {
                            total_span = id.span().join(g.span()).unwrap_or(g.span());
                            requires.push(Group(g));
                        },
                        _ => {
                            return syn::Error::new(
                                id.span(), "\"requires\" expects one parenthesized argument")
                                .to_compile_error();
                        }
                    }
                } else if id.to_string() == "ensures" {
                    match iter.next() {
                        Some(Group(g)) => {
                            total_span = id.span().join(g.span()).unwrap_or(g.span());
                            ensures.push(Group(g));
                        },
                        _ => {
                            return syn::Error::new(
                                id.span(), "\"ensures\" expects one parenthesized argument")
                                .to_compile_error();
                        }
                    }
                } else {
                    return syn::Error::new(id.span(), "invalid closure specification")
                        .to_compile_error();
                }

                match iter.next() {
                    Some(Punct(p)) => {
                        match p.as_char() {
                            ',' => {},
                            _ => {
                                return syn::Error::new(
                                    p.span(), "expected a comma here")
                                    .to_compile_error();
                            }
                        }
                    },
                    _ => {
                        return syn::Error::new(
                            total_span, "expected a comma after this")
                            .to_compile_error()
                    }
                }
            },

            _ => {
                let mut cl_toks = TokenStream::from(tok);
                cl_toks.extend(iter);

                match syn::parse2::<syn::ExprClosure>(cl_toks) {
                    Ok(cl_expr) => {
                        cl = Some(cl_expr);
                    },
                    Err(e) => {
                        return e.to_compile_error();
                    }
                }

                break;
            }
        }
    }

    let cl = cl.expect("closure must be parsed by now");

    if drop_spec {
        cl.into_token_stream()
    } else {
        let mut rewriter = rewriter::AstRewriter::new();

        let mut preconds: Vec<(untyped::SpecificationId,untyped::Assertion)> = Vec::new();
        let mut postconds: Vec<(untyped::SpecificationId,untyped::Assertion)> = Vec::new();

        let mut cl_annotations = TokenStream::new();

        for r in requires {
            let spec_id = rewriter.generate_spec_id();
            let precond = handle_result!(rewriter.parse_assertion(spec_id, r.into()));
            preconds.push((spec_id, precond));
            let spec_id_str = spec_id.to_string();
            cl_annotations.extend(quote! {
                #[prusti::pre_spec_id_ref = #spec_id_str]
            });
        }

        for e in ensures {
            let spec_id = rewriter.generate_spec_id();
            let postcond = handle_result!(rewriter.parse_assertion(spec_id, e.into()));
            postconds.push((spec_id, postcond));
            let spec_id_str = spec_id.to_string();
            cl_annotations.extend(quote! {
                #[prusti::post_spec_id_ref = #spec_id_str]
            });
        }

        let spec_toks = rewriter.generate_cl_spec(preconds, postconds);
        let toks = cl.to_token_stream();

        quote! { #cl_annotations #toks }
        // quote! {
        //     {
        //         if false {
        //             #spec_toks
        //         }
        //         #cl_annotations
        //         #toks
        //     }
        // }
    }
}
