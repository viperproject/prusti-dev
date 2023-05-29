#![deny(unused_must_use)]
#![feature(drain_filter)]
#![feature(box_patterns)]
#![feature(proc_macro_span)]
#![feature(if_let_guard)]
#![feature(assert_matches)]
// This Clippy chcek seems to be always wrong.
#![allow(clippy::iter_with_drain)]
#![warn(clippy::disallowed_types)]

#[macro_use]
mod common;
mod extern_spec_rewriter;
mod type_cond_specs;
mod parse_closure_macro;
mod parse_quote_spanned;
mod parse_ghost_macros;
mod predicate;
mod rewriter;
mod span_overrider;
mod spec_attribute_kind;
pub mod specifications;
mod type_model;
mod user_provided_type_params;
mod print_counterexample;

use parse_ghost_macros::{OnDropUnwind, WithFinally};
use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{quote, quote_spanned, ToTokens};
use rewriter::AstRewriter;
use std::convert::TryInto;
use syn::{spanned::Spanned, visit::Visit};

use crate::{
    common::{merge_generics, RewritableReceiver, SelfTypeRewriter},
    predicate::{is_predicate_macro, ParsedPredicate},
    specifications::preparser::{parse_prusti, parse_type_cond_spec, NestedSpec},
};
pub use extern_spec_rewriter::ExternSpecKind;
use parse_closure_macro::ClosureWithSpec;
pub use spec_attribute_kind::SpecAttributeKind;
use specifications::{common::SpecificationId, untyped};

pub const SPECS_VERSION: &str = env!("CARGO_PKG_VERSION");

macro_rules! handle_result {
    ($parse_result: expr) => {
        match $parse_result {
            Ok(data) => data,
            Err(err) => return err.to_compile_error(),
        }
    };
}

macro_rules! result_to_tokens {
    ($body:block) => {{
        let body = || $body;
        handle_result!(body())
    }};
}

fn extract_prusti_attributes(
    item: &mut untyped::AnyFnItem,
) -> Vec<(SpecAttributeKind, TokenStream)> {
    let mut prusti_attributes = Vec::new();
    let mut regular_attributes = Vec::new();
    for attr in item.attrs_mut().drain(0..) {
        if attr.path.segments.len() == 1
            || (attr.path.segments.len() == 2 && attr.path.segments[0].ident == "prusti_contracts")
        {
            let idx = attr.path.segments.len() - 1;
            if let Ok(attr_kind) = attr.path.segments[idx].ident.to_string().try_into() {
                let tokens = match attr_kind {
                    SpecAttributeKind::Requires
                    | SpecAttributeKind::Ensures
                    | SpecAttributeKind::NotRequire
                    | SpecAttributeKind::NotEnsure
                    | SpecAttributeKind::AfterExpiry
                    | SpecAttributeKind::AssertOnExpiry
                    | SpecAttributeKind::RefineSpec => {
                        // We need to drop the surrounding parenthesis to make the
                        // tokens identical to the ones passed by the native procedural
                        // macro call.
                        let mut iter = attr.tokens.into_iter();
                        let TokenTree::Group(group) = iter.next().unwrap() else { unreachable!() };
                        assert!(iter.next().is_none(), "Unexpected shape of an attribute.");
                        group.stream()
                    }
                    // Nothing to do for attributes without arguments.
                    SpecAttributeKind::Pure
                    | SpecAttributeKind::Terminates
                    | SpecAttributeKind::Trusted
                    | SpecAttributeKind::Predicate
                    | SpecAttributeKind::Verified
                    | SpecAttributeKind::NoPanic
                    | SpecAttributeKind::NoPanicEnsuresPostcondition => {
                        assert!(attr.tokens.is_empty(), "Unexpected shape of an attribute.");
                        attr.tokens
                    }
                    SpecAttributeKind::Invariant => unreachable!("type invariant on function"),
                    SpecAttributeKind::Model => unreachable!("model on function"),
                    SpecAttributeKind::PrintCounterexample => {
                        unreachable!("print_counterexample on function")
                    }
                };
                prusti_attributes.push((attr_kind, tokens));
            } else {
                regular_attributes.push(attr);
            }
        } else {
            regular_attributes.push(attr);
        }
    }
    *item.attrs_mut() = regular_attributes;
    prusti_attributes
}

/// Rewrite an item as required by *all* its specification attributes.
///
/// The first attribute (the outer one) needs to be passed via `attr_kind` and `attr` because
/// the compiler executes it as as a procedural macro attribute.
pub fn rewrite_prusti_attributes(
    outer_attr_kind: SpecAttributeKind,
    outer_attr_tokens: TokenStream,
    item_tokens: TokenStream,
) -> TokenStream {
    let mut item: untyped::AnyFnItem = handle_result!(syn::parse2(item_tokens));

    // Start with the outer attribute
    let mut prusti_attributes = vec![(outer_attr_kind, outer_attr_tokens)];

    // Collect the remaining Prusti attributes, removing them from `item`.
    prusti_attributes.extend(extract_prusti_attributes(&mut item));

    // make sure to also update the check in the predicate! handling method
    if prusti_attributes
        .iter()
        .any(|(ak, _)| ak == &SpecAttributeKind::Predicate)
    {
        return syn::Error::new(
            item.span(),
            "`predicate!` is incompatible with other Prusti attributes",
        )
        .to_compile_error();
    }

    let (generated_spec_items, generated_attributes) =
        handle_result!(generate_spec_and_assertions(prusti_attributes, &item));

    quote_spanned! {item.span()=>
        #(#generated_spec_items)*
        #(#generated_attributes)*
        #[prusti::specs_version = #SPECS_VERSION]
        #item
    }
}

type GeneratedResult = syn::Result<(Vec<syn::Item>, Vec<syn::Attribute>)>;

/// Generate spec items and attributes for `item` from the Prusti attributes
fn generate_spec_and_assertions(
    mut prusti_attributes: Vec<(SpecAttributeKind, TokenStream)>,
    item: &untyped::AnyFnItem,
) -> GeneratedResult {
    let mut generated_items = vec![];
    let mut generated_attributes = vec![];

    for (attr_kind, attr_tokens) in prusti_attributes.drain(..) {
        let rewriting_result = match attr_kind {
            SpecAttributeKind::Requires => generate_for_requires(attr_tokens, item),
            SpecAttributeKind::Ensures => generate_for_ensures(attr_tokens, item),
            SpecAttributeKind::NotRequire => generate_for_not_require(attr_tokens, item),
            SpecAttributeKind::NotEnsure => generate_for_not_ensure(attr_tokens, item),
            SpecAttributeKind::AfterExpiry => generate_for_after_expiry(attr_tokens, item),
            SpecAttributeKind::AssertOnExpiry => generate_for_assert_on_expiry(attr_tokens, item),
            SpecAttributeKind::Pure => generate_for_pure(attr_tokens, item),
            SpecAttributeKind::Verified => generate_for_verified(attr_tokens, item),
            SpecAttributeKind::Terminates => generate_for_terminates(attr_tokens, item),
            SpecAttributeKind::Trusted => generate_for_trusted(attr_tokens, item),
            SpecAttributeKind::NoPanic => generate_for_no_panic(attr_tokens, item),
            SpecAttributeKind::NoPanicEnsuresPostcondition => {
                generate_for_no_panic_ensures_postcondition(attr_tokens, item)
            }
            // Predicates are handled separately below; the entry in the SpecAttributeKind enum
            // only exists so we successfully parse it and emit an error in
            // `check_incompatible_attrs`; so we'll never reach here.
            SpecAttributeKind::Predicate => unreachable!(),
            SpecAttributeKind::Invariant => unreachable!(),
            SpecAttributeKind::RefineSpec => type_cond_specs::generate(attr_tokens, item),
            SpecAttributeKind::Model => unreachable!(),
            SpecAttributeKind::PrintCounterexample => unreachable!(),
        };
        let (new_items, new_attributes) = rewriting_result?;
        generated_items.extend(new_items);
        generated_attributes.extend(new_attributes);
    }

    Ok((generated_items, generated_attributes))
}

/// Generate spec items and attributes to typecheck the and later retrieve "requires" annotations.
fn generate_for_requires(attr: TokenStream, item: &untyped::AnyFnItem) -> GeneratedResult {
    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id = rewriter.generate_spec_id();
    let spec_id_str = spec_id.to_string();
    let spec_item =
        rewriter.process_assertion(rewriter::SpecItemType::Precondition, spec_id, attr, item)?;
    Ok((
        vec![spec_item],
        vec![parse_quote_spanned! {item.span()=>
            #[prusti::pre_spec_id_ref = #spec_id_str]
        }],
    ))
}

/// Generate spec items and attributes to typecheck and later retrieve
/// "not_require" annotations.
fn generate_for_not_require(attr: TokenStream, item: &untyped::AnyFnItem) -> GeneratedResult {
    let attr = quote! { prusti_broken_invariant(#attr) };
    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id = rewriter.generate_spec_id();
    let spec_id_str = spec_id.to_string();
    let spec_item = rewriter.process_assertion(
        rewriter::SpecItemType::BrokenPrecondition,
        spec_id,
        attr,
        item,
    )?;
    Ok((
        vec![spec_item],
        vec![parse_quote_spanned! {item.span()=>
            #[prusti::pre_broken_spec_id_ref = #spec_id_str]
        }],
    ))
}

/// Generate spec items and attributes to typecheck the and later retrieve "ensures" annotations.
fn generate_for_ensures(attr: TokenStream, item: &untyped::AnyFnItem) -> GeneratedResult {
    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id = rewriter.generate_spec_id();
    let spec_id_str = spec_id.to_string();
    let spec_item =
        rewriter.process_assertion(rewriter::SpecItemType::Postcondition, spec_id, attr, item)?;
    Ok((
        vec![spec_item],
        vec![parse_quote_spanned! {item.span()=>
            #[prusti::post_spec_id_ref = #spec_id_str]
        }],
    ))
}

/// Generate spec items and attributes to typecheck and later retrieve
/// "not_ensure" annotations.
fn generate_for_not_ensure(attr: TokenStream, item: &untyped::AnyFnItem) -> GeneratedResult {
    let attr = quote! { prusti_broken_invariant(#attr) };
    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id = rewriter.generate_spec_id();
    let spec_id_str = spec_id.to_string();
    let spec_item = rewriter.process_assertion(
        rewriter::SpecItemType::BrokenPostcondition,
        spec_id,
        attr,
        item,
    )?;
    Ok((
        vec![spec_item],
        vec![parse_quote_spanned! {item.span()=>
            #[prusti::post_broken_spec_id_ref = #spec_id_str]
        }],
    ))
}

/// Generate spec items and attributes to typecheck and later retrieve "after_expiry" annotations.
fn generate_for_after_expiry(attr: TokenStream, item: &untyped::AnyFnItem) -> GeneratedResult {
    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id = rewriter.generate_spec_id();
    let spec_id_str = spec_id.to_string();
    let spec_item = rewriter.process_pledge(spec_id, attr, item)?;
    Ok((
        vec![spec_item],
        vec![parse_quote_spanned! {item.span()=>
            #[prusti::pledge_spec_id_ref = #spec_id_str]
        }],
    ))
}

/// Generate spec items and attributes to typecheck and later retrieve "after_expiry" annotations.
fn generate_for_assert_on_expiry(attr: TokenStream, item: &untyped::AnyFnItem) -> GeneratedResult {
    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id_lhs = rewriter.generate_spec_id();
    let spec_id_lhs_str = spec_id_lhs.to_string();
    let spec_id_rhs = rewriter.generate_spec_id();
    let spec_id_rhs_str = spec_id_rhs.to_string();
    let (spec_item_lhs, spec_item_rhs) =
        rewriter.process_assert_pledge(spec_id_lhs, spec_id_rhs, attr, item)?;
    Ok((
        vec![spec_item_lhs, spec_item_rhs],
        vec![
            parse_quote_spanned! {item.span()=>
                #[prusti::assert_pledge_spec_id_ref_lhs = #spec_id_lhs_str]
            },
            parse_quote_spanned! {item.span()=>
                #[prusti::assert_pledge_spec_id_ref_rhs = #spec_id_rhs_str]
            },
        ],
    ))
}

/// Generate spec items and attributes to typecheck and later retrieve "terminates" annotations.
fn generate_for_terminates(mut attr: TokenStream, item: &untyped::AnyFnItem) -> GeneratedResult {
    if attr.is_empty() {
        attr = quote! { Int::new(1) };
    } else {
        let mut attr_iter = attr.clone().into_iter();
        let first = attr_iter.next();
        if let Some(TokenTree::Ident(ident)) = first {
            if attr_iter.next().is_none() && ident == "trusted" {
                attr = quote! { prusti_terminates_trusted() }
            }
        }
    }

    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id = rewriter.generate_spec_id();
    let spec_id_str = spec_id.to_string();
    let spec_item =
        rewriter.process_assertion(rewriter::SpecItemType::Termination, spec_id, attr, item)?;

    Ok((
        vec![spec_item],
        vec![parse_quote_spanned! {item.span()=>
            #[prusti::terminates_spec_id_ref = #spec_id_str]
        }],
    ))
}

/// Generate spec items and attributes to typecheck and later retrieve "pure" annotations.
fn generate_for_pure(attr: TokenStream, item: &untyped::AnyFnItem) -> GeneratedResult {
    if !attr.is_empty() {
        return Err(syn::Error::new(
            attr.span(),
            "the `#[pure]` attribute does not take parameters",
        ));
    }

    Ok((
        vec![],
        vec![parse_quote_spanned! {item.span()=>
            #[prusti::pure]
        }],
    ))
}

/// Generate spec items and attributes to typecheck and later retrieve "verified" annotations.
fn generate_for_verified(attr: TokenStream, item: &untyped::AnyFnItem) -> GeneratedResult {
    if !attr.is_empty() {
        return Err(syn::Error::new(
            attr.span(),
            "the `#[verified]` attribute does not take parameters",
        ));
    }

    Ok((
        vec![],
        vec![parse_quote_spanned! {item.span()=>
            #[prusti::verified]
        }],
    ))
}

/// Generate spec items and attributes to typecheck and later retrieve "pure" annotations, but encoded as a referenced separate function that type-conditional spec refinements can apply trait bounds to.
fn generate_for_pure_refinements(item: &untyped::AnyFnItem) -> GeneratedResult {
    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id = rewriter.generate_spec_id();
    let spec_id_str = spec_id.to_string();
    let spec_item = rewriter.process_pure_refinement(spec_id, item)?;

    Ok((
        vec![spec_item],
        vec![parse_quote_spanned! {item.span()=>
            #[prusti::pure_spec_id_ref = #spec_id_str]
        }],
    ))
}

/// Generate spec items and attributes to typecheck and later retrieve "trusted" annotations.
fn generate_for_trusted(attr: TokenStream, item: &untyped::AnyFnItem) -> GeneratedResult {
    if !attr.is_empty() {
        return Err(syn::Error::new(
            attr.span(),
            "the `#[trusted]` attribute does not take parameters",
        ));
    }

    Ok((
        vec![],
        vec![parse_quote_spanned! {item.span()=>
            #[prusti::trusted]
        }],
    ))
}

/// Generate spec items and attributes to typecheck and later retrieve
/// "no_panic" annotations.
fn generate_for_no_panic(attr: TokenStream, item: &untyped::AnyFnItem) -> GeneratedResult {
    if !attr.is_empty() {
        return Err(syn::Error::new(
            attr.span(),
            "the `#[no_panic]` attribute does not take parameters",
        ));
    }

    Ok((
        vec![],
        vec![parse_quote_spanned! {item.span()=>
            #[prusti::no_panic]
        }],
    ))
}

/// Generate spec items and attributes to typecheck and later retrieve
/// "no_panic_ensures_postcondition" annotations.
fn generate_for_no_panic_ensures_postcondition(
    attr: TokenStream,
    item: &untyped::AnyFnItem,
) -> GeneratedResult {
    if !attr.is_empty() {
        return Err(syn::Error::new(
            attr.span(),
            "the `#[no_panic_ensures_postcondition]` attribute does not take parameters",
        ));
    }

    Ok((
        vec![],
        vec![parse_quote_spanned! {item.span()=>
            #[prusti::no_panic_ensures_postcondition]
        }],
    ))
}

/// Generate spec items and attributes to typecheck and later retrieve "trusted" annotations.
fn generate_for_trusted_for_types(attr: TokenStream, item: &syn::DeriveInput) -> GeneratedResult {
    if !attr.is_empty() {
        return Err(syn::Error::new(
            attr.span(),
            "the `#[trusted]` attribute does not take parameters",
        ));
    }
    // TODO: reduce duplication with `invariant`
    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id = rewriter.generate_spec_id();
    let spec_id_str = spec_id.to_string();

    let item_span = item.span();
    let item_ident = item.ident.clone();
    let item_name = syn::Ident::new(
        &format!("prusti_trusted_item_{item_ident}_{spec_id}"),
        item_span,
    );

    let spec_item: syn::ItemFn = parse_quote_spanned! {item_span=>
        #[allow(unused_variables, dead_code, non_snake_case)]
        #[prusti::spec_only]
        #[prusti::trusted_type]
        #[prusti::spec_id = #spec_id_str]
        fn #item_name(self) {}
    };

    let generics = &item.generics;
    let generics_idents = generics
        .params
        .iter()
        .map(|generic_param| match generic_param {
            syn::GenericParam::Type(param) => syn::GenericParam::Type(syn::TypeParam {
                attrs: Vec::new(),
                bounds: syn::punctuated::Punctuated::new(),
                colon_token: None,
                default: None,
                eq_token: None,
                ident: param.ident.clone(),
            }),
            syn::GenericParam::Lifetime(param) => syn::GenericParam::Lifetime(syn::LifetimeDef {
                attrs: Vec::new(),
                bounds: syn::punctuated::Punctuated::new(),
                colon_token: None,
                lifetime: param.lifetime.clone(),
            }),
            syn::GenericParam::Const(param) => syn::GenericParam::Const(syn::ConstParam {
                attrs: Vec::new(),
                colon_token: param.colon_token,
                const_token: param.const_token,
                default: None,
                eq_token: None,
                ident: param.ident.clone(),
                ty: param.ty.clone(),
            }),
        })
        .collect::<syn::punctuated::Punctuated<_, syn::Token![,]>>();
    // TODO: similarly to extern_specs, don't generate an actual impl
    let item_impl: syn::ItemImpl = parse_quote_spanned! {item_span=>
        impl #generics #item_ident <#generics_idents> {
            #spec_item
        }
    };

    Ok((vec![syn::Item::Impl(item_impl)], vec![]))
}

pub fn body_variant(tokens: TokenStream) -> TokenStream {
    generate_expression_closure(&AstRewriter::process_loop_variant, tokens)
}

pub fn body_invariant(tokens: TokenStream) -> TokenStream {
    generate_expression_closure(&AstRewriter::process_loop_invariant, tokens)
}

pub fn prusti_assertion(tokens: TokenStream) -> TokenStream {
    generate_expression_closure(&AstRewriter::process_prusti_assertion, tokens)
}

pub fn prusti_assume(tokens: TokenStream) -> TokenStream {
    generate_expression_closure(&AstRewriter::process_prusti_assumption, tokens)
}

pub fn prusti_refutation(tokens: TokenStream) -> TokenStream {
    generate_expression_closure(&AstRewriter::process_prusti_refutation, tokens)
}

pub fn prusti_structural_assert(tokens: TokenStream) -> TokenStream {
    generate_expression_closure(&AstRewriter::process_prusti_structural_assertion, tokens)
}

pub fn prusti_structural_assume(tokens: TokenStream) -> TokenStream {
    generate_expression_closure(&AstRewriter::process_prusti_structural_assumption, tokens)
}

/// Generates the TokenStream encoding an expression using prusti syntax
/// Used for body invariants, assertions, and assumptions
fn generate_expression_closure(
    fun: &dyn Fn(&mut AstRewriter, SpecificationId, TokenStream) -> syn::Result<TokenStream>,
    tokens: TokenStream,
) -> TokenStream {
    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id = rewriter.generate_spec_id();
    let closure = handle_result!(fun(&mut rewriter, spec_id, tokens));
    let callsite_span = Span::call_site();
    quote_spanned! {callsite_span=>
        #[allow(unused_must_use, unused_variables, unused_braces, unused_parens)]
        #[prusti::specs_version = #SPECS_VERSION]
        if false {
            #closure
        }
    }
}

fn prusti_specification_expression(
    tokens: TokenStream,
) -> syn::Result<(SpecificationId, TokenStream)> {
    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id = rewriter.generate_spec_id();
    let closure = rewriter.process_prusti_specification_expression(spec_id, tokens)?;
    let callsite_span = Span::call_site();
    let tokens = quote_spanned! {callsite_span=>
        #[allow(unused_must_use, unused_variables, unused_braces, unused_parens)]
        #[prusti::specs_version = #SPECS_VERSION]
        if false {
            #closure
        }
    };
    Ok((spec_id, tokens))
}

pub fn closure(tokens: TokenStream) -> TokenStream {
    let cl_spec: ClosureWithSpec = handle_result!(syn::parse(tokens.into()));
    let callsite_span = Span::call_site();

    let mut rewriter = rewriter::AstRewriter::new();

    let mut preconds: Vec<(SpecificationId, syn::Expr)> = vec![];
    let mut postconds: Vec<(SpecificationId, syn::Expr)> = vec![];

    let mut cl_annotations = TokenStream::new();

    for r in cl_spec.pres {
        let spec_id = rewriter.generate_spec_id();
        let precond =
            handle_result!(rewriter.process_closure_assertion(spec_id, r.to_token_stream(),));
        preconds.push((spec_id, precond));
        let spec_id_str = spec_id.to_string();
        cl_annotations.extend(quote_spanned! {callsite_span=>
            #[prusti::pre_spec_id_ref = #spec_id_str]
        });
    }

    for e in cl_spec.posts {
        let spec_id = rewriter.generate_spec_id();
        let postcond =
            handle_result!(rewriter.process_closure_assertion(spec_id, e.to_token_stream(),));
        postconds.push((spec_id, postcond));
        let spec_id_str = spec_id.to_string();
        cl_annotations.extend(quote_spanned! {callsite_span=>
            #[prusti::post_spec_id_ref = #spec_id_str]
        });
    }

    let syn::ExprClosure {
        attrs,
        asyncness,
        movability,
        capture,
        or1_token,
        inputs,
        or2_token,
        output,
        body,
    } = cl_spec.cl;

    let output_type: syn::Type = match output {
        syn::ReturnType::Default => {
            return syn::Error::new(output.span(), "closure must specify return type")
                .to_compile_error();
        }
        syn::ReturnType::Type(_, ref ty) => (**ty).clone(),
    };

    let (spec_toks_pre, spec_toks_post) =
        handle_result!(rewriter.process_closure(inputs.clone(), output_type, preconds, postconds,));

    let mut attrs_ts = TokenStream::new();
    for a in attrs {
        attrs_ts.extend(a.into_token_stream());
    }

    quote_spanned! {callsite_span=>
        {
            #[allow(unused_variables, unused_braces, unused_parens)]
            #[prusti::closure]
            #[prusti::specs_version = #SPECS_VERSION]
            #cl_annotations #attrs_ts
            let _prusti_closure =
                #asyncness #movability #capture
                #or1_token #inputs #or2_token #output
                {
                    #[allow(unused_must_use, unused_braces, unused_parens)]
                    if false {
                        #spec_toks_pre
                    }
                    let result = #body ;
                    #[allow(unused_must_use, unused_braces, unused_parens)]
                    if false {
                        #spec_toks_post
                    }
                    result
                };
            _prusti_closure
        }
    }
}

pub fn refine_trait_spec(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    let mut impl_block: syn::ItemImpl = handle_result!(syn::parse2(tokens));
    let impl_generics = &impl_block.generics;

    let trait_path: syn::TypePath = match &impl_block.trait_ {
        Some((_, trait_path, _)) => parse_quote_spanned!(trait_path.span()=>#trait_path),
        None => handle_result!(Err(syn::Error::new(
            impl_block.span(),
            "Can refine trait specifications only on trait implementation blocks"
        ))),
    };

    let self_type: &syn::Type = &impl_block.self_ty;

    let mut new_items = Vec::new();
    let mut generated_spec_items = Vec::new();
    for item in impl_block.items {
        match item {
            syn::ImplItem::Method(method) => {
                let mut method_item = untyped::AnyFnItem::ImplMethod(method);
                let prusti_attributes: Vec<_> = extract_prusti_attributes(&mut method_item);

                let illegal_attribute_span = prusti_attributes
                    .iter()
                    .filter(|(kind, _)| kind == &SpecAttributeKind::RefineSpec)
                    .map(|(_, tokens)| tokens.span())
                    .next();
                if let Some(span) = illegal_attribute_span {
                    let err = Err(syn::Error::new(
                        span,
                        "Type-conditional spec refinements in trait spec refinements not supported",
                    ));
                    handle_result!(err);
                }

                let (spec_items, generated_attributes) = handle_result!(
                    generate_spec_and_assertions(prusti_attributes, &method_item)
                );

                spec_items
                    .into_iter()
                    .map(|spec_item| match spec_item {
                        syn::Item::Fn(spec_item_fn) => spec_item_fn,
                        x => unimplemented!("Unexpected variant: {:?}", x),
                    })
                    .for_each(|spec_item_fn| generated_spec_items.push(spec_item_fn));

                let new_item = parse_quote_spanned! {method_item.span()=>
                    #(#generated_attributes)*
                    #method_item
                };
                new_items.push(new_item);
            }
            syn::ImplItem::Macro(makro) if is_predicate_macro(&makro) => {
                let parsed_predicate =
                    handle_result!(predicate::parse_predicate_in_impl(makro.mac.tokens.clone()));

                let ParsedPredicate::Impl(predicate) = parsed_predicate else { unreachable!() };

                // Patch spec function: Rewrite self with _self: <SpecStruct>
                let syn::Item::Fn(spec_function) = predicate.spec_function else { unreachable!() };
                generated_spec_items.push(spec_function);

                // Add patched predicate function to new items
                new_items.push(syn::ImplItem::Method(predicate.patched_function));
            }
            _ => new_items.push(item),
        }
    }

    // Patch the spec items (merge generics, handle associated types, rewrite receiver)
    for generated_spec_item in generated_spec_items.iter_mut() {
        merge_generics(&mut generated_spec_item.sig.generics, impl_generics);
        generated_spec_item.rewrite_self_type(self_type, Some(&trait_path));
        generated_spec_item.rewrite_receiver(self_type);
    }

    impl_block.items = new_items;
    quote_spanned! {impl_block.span()=>
        #(#generated_spec_items)*
        #[prusti::specs_version = #SPECS_VERSION]
        #impl_block
    }
}

pub fn trusted(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    if !attr.is_empty() {
        return syn::Error::new(
            attr.span(),
            "the `#[trusted]` attribute does not take parameters",
        )
        .to_compile_error();
    }

    // `#[trusted]` can be applied to both types and to methods, figure out
    // which one by trying to parse a `DeriveInput`.
    if syn::parse2::<syn::DeriveInput>(tokens.clone()).is_ok() {
        // TODO: reduce duplication with `invariant`
        let mut rewriter = rewriter::AstRewriter::new();
        let spec_id = rewriter.generate_spec_id();
        let spec_id_str = spec_id.to_string();

        let item: syn::DeriveInput = handle_result!(syn::parse2(tokens));
        let item_span = item.span();

        // clippy false positive (https://github.com/rust-lang/rust-clippy/issues/10577)
        #[allow(clippy::redundant_clone)]
        let item_ident = item.ident.clone();

        let item_name = syn::Ident::new(
            &format!("prusti_trusted_item_{item_ident}_{spec_id}"),
            item_span,
        );

        let spec_item: syn::ItemFn = parse_quote_spanned! {item_span=>
            #[allow(unused_variables, dead_code, non_snake_case)]
            #[prusti::spec_only]
            #[prusti::trusted_type]
            #[prusti::spec_id = #spec_id_str]
            fn #item_name(self) {}
        };

        let generics = &item.generics;
        let generics_idents = generics
            .params
            .iter()
            .map(|generic_param| match generic_param {
                syn::GenericParam::Type(param) => syn::GenericParam::Type(syn::TypeParam {
                    attrs: Vec::new(),
                    bounds: syn::punctuated::Punctuated::new(),
                    colon_token: None,
                    default: None,
                    eq_token: None,
                    ident: param.ident.clone(),
                }),
                syn::GenericParam::Lifetime(param) => {
                    syn::GenericParam::Lifetime(syn::LifetimeDef {
                        attrs: Vec::new(),
                        bounds: syn::punctuated::Punctuated::new(),
                        colon_token: None,
                        lifetime: param.lifetime.clone(),
                    })
                }
                syn::GenericParam::Const(param) => syn::GenericParam::Const(syn::ConstParam {
                    attrs: Vec::new(),
                    colon_token: param.colon_token,
                    const_token: param.const_token,
                    default: None,
                    eq_token: None,
                    ident: param.ident.clone(),
                    ty: param.ty.clone(),
                }),
            })
            .collect::<syn::punctuated::Punctuated<_, syn::Token![,]>>();
        // TODO: similarly to extern_specs, don't generate an actual impl
        let item_impl: syn::ItemImpl = parse_quote_spanned! {item_span=>
            impl #generics #item_ident <#generics_idents> {
                #spec_item
            }
        };
        quote_spanned! { item_span =>
            #[prusti::specs_version = #SPECS_VERSION]
            #item
            #item_impl
        }
    } else {
        rewrite_prusti_attributes(SpecAttributeKind::Trusted, attr, tokens)
    }
}

pub fn invariant(attr: TokenStream, tokens: TokenStream, is_structural: bool) -> TokenStream {
    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id = rewriter.generate_spec_id();
    let spec_id_str = spec_id.to_string();

    let item: syn::DeriveInput = handle_result!(syn::parse2(tokens));
    let item_span = item.span();

    // clippy false positive (https://github.com/rust-lang/rust-clippy/issues/10577)
    #[allow(clippy::redundant_clone)]
    let item_ident = item.ident.clone();
    let item_name_structural = if is_structural {
        "structural"
    } else {
        "non_structural"
    };
    let item_name = syn::Ident::new(
        &format!("prusti_invariant_item_{item_name_structural}_{item_ident}_{spec_id}"),
        item_span,
    );

    let attr = handle_result!(parse_prusti(attr));

    let is_structural_tokens = if is_structural {
        quote_spanned!(item_span => #[prusti::type_invariant_structural])
    } else {
        quote_spanned!(item_span => #[prusti::type_invariant_non_structural])
    };
    // TODO: move some of this to AstRewriter?
    // see AstRewriter::generate_spec_item_fn for explanation of syntax below
    let spec_item: syn::ItemFn = parse_quote_spanned! {item_span=>
        #[allow(unused_must_use, unused_parens, unused_variables, dead_code, non_snake_case)]
        #[prusti::spec_only]
        #[prusti::type_invariant_spec]
        #is_structural_tokens
        #[prusti::spec_id = #spec_id_str]
        fn #item_name(self) -> bool {
            !!((#attr) : bool)
        }
    };

    // clippy false positive (https://github.com/rust-lang/rust-clippy/issues/10577)
    #[allow(clippy::redundant_clone)]
    let generics = item.generics.clone();

    let generics_idents = generics
        .params
        .iter()
        .filter_map(|generic_param| match generic_param {
            syn::GenericParam::Type(type_param) => Some(type_param.ident.clone()),
            _ => None,
        })
        .collect::<syn::punctuated::Punctuated<_, syn::Token![,]>>();
    // TODO: similarly to extern_specs, don't generate an actual impl
    let item_impl: syn::ItemImpl = parse_quote_spanned! {item_span=>
        impl #generics #item_ident < #generics_idents > {
            #spec_item
        }
    };
    quote_spanned! { item_span =>
        #[prusti::specs_version = #SPECS_VERSION]
        #item
        #item_impl
    }
}

pub fn extern_spec(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    result_to_tokens!({
        let item: syn::Item = syn::parse2(tokens)?;
        let mod_path: syn::Path = Some(attr)
            .filter(|attr| !attr.is_empty())
            .map(syn::parse2)
            .transpose()?
            .unwrap_or_else(|| syn::Path {
                leading_colon: None,
                segments: syn::punctuated::Punctuated::new(),
            });
        match item {
            syn::Item::Impl(item_impl) => {
                if !mod_path.segments.is_empty() {
                    return Err(syn::Error::new(
                        mod_path.span(),
                        "extern_spec does not take a path argument for impls--you can qualify the involved types directly",
                    ));
                }
                extern_spec_rewriter::impls::rewrite_extern_spec(&item_impl)
            }
            syn::Item::Trait(item_trait) => {
                extern_spec_rewriter::traits::rewrite_extern_spec(&item_trait, mod_path)
            }
            syn::Item::Mod(item_mod) => {
                extern_spec_rewriter::mods::rewrite_mod(&item_mod, mod_path)
            }
            syn::Item::ForeignMod(item_foreign_mod) => {
                extern_spec_rewriter::foreign_mods::rewrite_extern_spec(
                    &item_foreign_mod,
                    &mod_path,
                )
            }
            // we're expecting function stubs, so they aren't represented as Item::Fn
            syn::Item::Verbatim(stub_tokens) => {
                extern_spec_rewriter::functions::rewrite_stub(&stub_tokens, &mod_path, false)
            }
            _ => Err(syn::Error::new(
                Span::call_site(), // this covers the entire macro invocation, unlike attr.span() which changes to only cover arguments if possible
                "Extern specs cannot be attached to this item",
            )),
        }
    })
}

pub fn predicate(tokens: TokenStream) -> TokenStream {
    let parsed = handle_result!(predicate::parse_predicate(tokens));
    parsed.into_token_stream()
}

pub fn rewrite_prusti_attributes_for_types(
    outer_attr_kind: SpecAttributeKind,
    outer_attr_tokens: TokenStream,
    item_tokens: TokenStream,
) -> TokenStream {
    let mut item: syn::DeriveInput = handle_result!(syn::parse2(item_tokens));

    // Start with the outer attribute
    let mut prusti_attributes = vec![(outer_attr_kind, outer_attr_tokens)];

    // Collect the remaining Prusti attributes, removing them from `item`.
    prusti_attributes.extend(extract_prusti_attributes_for_types(&mut item));

    if prusti_attributes.len() > 1
        && prusti_attributes
            .iter()
            .any(|(ak, _)| ak == &SpecAttributeKind::Trusted)
    {
        return syn::Error::new(
            item.span(),
            "`trusted!` is incompatible with other Prusti attributes",
        )
        .to_compile_error();
    }

    // we order the attributes to ensure a model attribute is processed first
    prusti_attributes.sort_by(|(ak1, _), (ak2, _)| ak1.cmp(ak2));

    let (generated_spec_items, generated_attributes) = handle_result!(
        generate_spec_and_assertions_for_types(prusti_attributes, &mut item)
    );

    quote_spanned! {item.span()=>
        #(#generated_attributes)*
        #item
        #(#generated_spec_items)*
    }
}

fn extract_prusti_attributes_for_types(
    item: &mut syn::DeriveInput,
) -> Vec<(SpecAttributeKind, TokenStream)> {
    let mut prusti_attributes = Vec::new();
    let mut regular_attributes = Vec::new();
    for attr in item.attrs.drain(0..) {
        if attr.path.segments.len() == 1 {
            if let Ok(attr_kind) = attr.path.segments[0].ident.to_string().try_into() {
                let tokens = match attr_kind {
                    SpecAttributeKind::Requires => unreachable!("requires on type"),
                    SpecAttributeKind::Ensures => unreachable!("ensures on type"),
                    SpecAttributeKind::AfterExpiry => unreachable!("after_expiry on type"),
                    SpecAttributeKind::AssertOnExpiry => unreachable!("assert_on_expiry on type"),
                    SpecAttributeKind::RefineSpec => unreachable!("refine_spec on type"),
                    SpecAttributeKind::Pure => unreachable!("pure on type"),
                    SpecAttributeKind::Verified => unreachable!("verified on type"),
                    SpecAttributeKind::Invariant => unreachable!("invariant on type"),
                    SpecAttributeKind::Predicate => unreachable!("predicate on type"),
                    SpecAttributeKind::Terminates => unreachable!("terminates on type"),
                    SpecAttributeKind::NoPanic => unreachable!("no_panic on type"),
                    SpecAttributeKind::NoPanicEnsuresPostcondition => {
                        unreachable!("no_panic_ensures_postcondition on type")
                    }
                    SpecAttributeKind::NotRequire => {
                        unreachable!("not_require on type")
                    }
                    SpecAttributeKind::NotEnsure => {
                        unreachable!("not_ensure on type")
                    }
                    SpecAttributeKind::Trusted | SpecAttributeKind::Model => {
                        assert!(attr.tokens.is_empty(), "Unexpected shape of an attribute.");
                        attr.tokens
                    }
                    SpecAttributeKind::PrintCounterexample => {
                        // We need to drop the surrounding parenthesis to make the
                        // tokens identical to the ones passed by the native procedural
                        // macro call.
                        let mut iter = attr.tokens.into_iter();
                        let TokenTree::Group(group) = iter.next().unwrap() else { unreachable!() };
                        group.stream()
                    }
                };
                prusti_attributes.push((attr_kind, tokens));
            } else {
                regular_attributes.push(attr);
            }
        } else {
            regular_attributes.push(attr);
        }
    }
    item.attrs = regular_attributes;
    prusti_attributes
}

/// Generate spec items and attributes for `item` from the Prusti attributes
fn generate_spec_and_assertions_for_types(
    mut prusti_attributes: Vec<(SpecAttributeKind, TokenStream)>,
    item: &mut syn::DeriveInput,
) -> GeneratedResult {
    let mut generated_items = vec![];
    let mut generated_attributes = vec![];

    for (attr_kind, attr_tokens) in prusti_attributes.drain(..) {
        let rewriting_result = match attr_kind {
            SpecAttributeKind::Requires => unreachable!(),
            SpecAttributeKind::Ensures => unreachable!(),
            SpecAttributeKind::AfterExpiry => unreachable!(),
            SpecAttributeKind::AssertOnExpiry => unreachable!(),
            SpecAttributeKind::Pure => unreachable!(),
            SpecAttributeKind::Verified => unreachable!(),
            SpecAttributeKind::Predicate => unreachable!(),
            SpecAttributeKind::Invariant => unreachable!(),
            SpecAttributeKind::RefineSpec => unreachable!(),
            SpecAttributeKind::Terminates => unreachable!(),
            SpecAttributeKind::Trusted => generate_for_trusted_for_types(attr_tokens, item),
            SpecAttributeKind::NoPanic => unreachable!(),
            SpecAttributeKind::NoPanicEnsuresPostcondition => unreachable!(),
            SpecAttributeKind::NotRequire => unreachable!(),
            SpecAttributeKind::NotEnsure => unreachable!(),
            SpecAttributeKind::Model => generate_for_model(attr_tokens, item),
            SpecAttributeKind::PrintCounterexample => {
                generate_for_print_counterexample(attr_tokens, item)
            }
        };
        let (new_items, new_attributes) = rewriting_result?;
        generated_items.extend(new_items);
        generated_attributes.extend(new_attributes);
    }

    Ok((generated_items, generated_attributes))
}

/// Generate spec items and attributes to typecheck and later retrieve "model" annotations.
fn generate_for_model(attr: TokenStream, item: &mut syn::DeriveInput) -> GeneratedResult {
    match syn::Item::from(item.clone()) {
        syn::Item::Struct(item_struct) => {
            match type_model::rewrite(item_struct) {
                Ok(result) => {
                    match result.first() {
                        Some(syn::Item::Struct(new_item)) => {
                            *item = syn::DeriveInput::from(new_item.clone()); //the internal model replaces the original struct
                            Ok((vec![result[1].clone(), result[2].clone()], vec![]))
                        }
                        _ => unreachable!(),
                    }
                }
                Err(err) => Err(err),
            }
        }
        _ => Err(syn::Error::new(
            attr.span(),
            "Only structs can be attributed with a type model",
        )),
    }
}

/// Generate spec items and attributes to typecheck and later retrieve "print_counterexample" annotations.
fn generate_for_print_counterexample(
    attr: TokenStream,
    item: &mut syn::DeriveInput,
) -> GeneratedResult {
    match syn::Item::from(item.clone()) {
        syn::Item::Struct(item_struct) => {
            match print_counterexample::rewrite_struct(attr, item_struct) {
                Ok(result) => Ok((result, vec![])),
                Err(err) => Err(err),
            }
        }
        syn::Item::Enum(item_enum) => {
            match print_counterexample::rewrite_enum(attr, item_enum) {
                Ok(result) => {
                    match result.first() {
                        Some(syn::Item::Enum(new_item)) => {
                            *item = syn::DeriveInput::from(new_item.clone()); //print_counterexample removes all attributes inside the enum
                            Ok((vec![result[1].clone()], vec![]))
                        }
                        _ => unreachable!(),
                    }
                }
                Err(err) => Err(err),
            }
        }
        _ => Err(syn::Error::new(
            attr.span(),
            "Only structs and enums can be attributed with a custom counterexample print",
        )),
    }
}

pub fn type_model(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    if syn::parse2::<syn::DeriveInput>(tokens.clone()).is_ok() {
        rewrite_prusti_attributes_for_types(SpecAttributeKind::Model, attr, tokens)
    } else {
        syn::Error::new(
            attr.span(),
            "Only structs can be attributed with a type model",
        )
        .to_compile_error()
    }
}

pub fn print_counterexample(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    if syn::parse2::<syn::DeriveInput>(tokens.clone()).is_ok() {
        rewrite_prusti_attributes_for_types(SpecAttributeKind::PrintCounterexample, attr, tokens)
    } else {
        syn::Error::new(
            attr.span(),
            "Only structs and enums can be attributed with print_counterexample",
        )
        .to_compile_error()
    }
}

fn ghost_with_annotation(
    tokens: TokenStream,
    annotation: TokenStream,
    wrap_result_in_ghost: bool,
    begin_marker: TokenStream,
    end_marker: TokenStream,
    spec_id: Option<SpecificationId>,
) -> TokenStream {
    let callsite_span = Span::call_site();

    let spec_id = if let Some(spec_id) = spec_id {
        spec_id
    } else {
        let mut rewriter = rewriter::AstRewriter::new();
        rewriter.generate_spec_id()
    };
    let spec_id_str = spec_id.to_string();

    let make_closure = |kind| {
        quote! {
            #[allow(unused_must_use, unused_variables, unused_braces, unused_parens)]
            if false {
                #[prusti::spec_only]
                #[prusti::#kind]
                #[prusti::spec_id = #spec_id_str]
                || -> () {};
            }
        }
    };

    struct Visitor {
        loops: Vec<(Option<syn::Ident>, Span)>,
        breaks: Vec<(Option<syn::Ident>, Span)>,
        returns: Option<Span>,
    }

    impl<'ast> Visit<'ast> for Visitor {
        fn visit_expr_for_loop(&mut self, ex: &'ast syn::ExprForLoop) {
            let e = ex.clone();
            let lbl = e.label.map(|c| c.name.ident);
            let span = e.body.brace_token.span;
            self.loops.push((lbl, span));
            syn::visit::visit_expr_for_loop(self, ex);
        }
        fn visit_expr_while(&mut self, ex: &'ast syn::ExprWhile) {
            let e = ex.clone();
            let lbl = e.label.map(|c| c.name.ident);
            let span = e.body.brace_token.span;
            self.loops.push((lbl, span));
            syn::visit::visit_expr_while(self, ex);
        }
        fn visit_expr_loop(&mut self, ex: &'ast syn::ExprLoop) {
            let e = ex.clone();
            let lbl = e.label.map(|c| c.name.ident);
            let span = e.body.brace_token.span;
            self.loops.push((lbl, span));
            syn::visit::visit_expr_loop(self, ex);
        }
        fn visit_expr_continue(&mut self, ex: &'ast syn::ExprContinue) {
            let e = ex.clone();
            let lbl = e.label.map(|c| c.ident);
            self.breaks.push((lbl, ex.span()));
            syn::visit::visit_expr_continue(self, ex);
        }
        fn visit_expr_break(&mut self, ex: &'ast syn::ExprBreak) {
            let e = ex.clone();
            let lbl = e.label.map(|c| c.ident);
            self.breaks.push((lbl, ex.span()));
            syn::visit::visit_expr_break(self, ex);
        }
        fn visit_expr_return(&mut self, e: &'ast syn::ExprReturn) {
            let e = e.clone();
            self.returns = Some(e.span());
        }
    }

    let mut visitor = Visitor {
        loops: vec![],
        breaks: vec![],
        returns: None,
    };

    let tokens = quote! {
        {#tokens}
    };

    let input = syn::parse::<syn::Block>(tokens.clone().into()).unwrap();

    visitor.visit_block(&input);

    let mut exit_errors = visitor.returns.into_iter().collect::<Vec<_>>();

    'breaks: for (break_label, break_span) in visitor.breaks.iter() {
        for (loop_label, loop_span) in visitor.loops.iter() {
            let loop_span = loop_span.unwrap();
            let label_match = break_label == loop_label || break_label.is_none();
            let break_inside = loop_span.join(break_span.unwrap()).unwrap().eq(&loop_span);
            if label_match && break_inside {
                continue 'breaks;
            }
        }
        exit_errors.push(*break_span);
    }

    let begin = make_closure(begin_marker);
    let end = make_closure(end_marker);
    let ghost_result = if wrap_result_in_ghost {
        quote! {Ghost::new(#tokens)}
    } else {
        quote! {#tokens}
    };

    if exit_errors.is_empty() {
        quote_spanned! {callsite_span=>
            {
                #begin
                #annotation
                #[prusti::specs_version = #SPECS_VERSION]
                let ghost_result = #ghost_result;
                #end
                ghost_result
            }
        }
    } else {
        let mut syn_errors = quote! {};
        for error in exit_errors {
            let error =
                syn::Error::new(error, "Can't leave the ghost block early").to_compile_error();
            syn_errors = quote! {
                #syn_errors
                #error
            }
        }
        syn_errors
    }
}

pub fn ghost(tokens: TokenStream) -> TokenStream {
    ghost_with_annotation(
        tokens,
        quote! {},
        true,
        quote! {ghost_begin},
        quote! {ghost_end},
        None,
    )
}

macro_rules! parse_expressions {
    ($tokens: expr, $separator: ty => $( $expr:ident ),* ) => {
        let parser = syn::punctuated::Punctuated::<syn::Expr, $separator>::parse_terminated;
        let expressions = handle_result!(syn::parse::Parser::parse2(parser, $tokens));
        let mut expressions: Vec<_> = expressions.into_pairs().map(|pair| pair.into_value()).collect();
        expressions.reverse();
        $(
            let $expr = handle_result!(
                expressions
                    .pop()
                    .ok_or_else(|| syn::Error::new(Span::call_site(), "Expected more expressions"))
            );
        )*
    }
}

pub fn on_drop_unwind(tokens: TokenStream) -> TokenStream {
    let OnDropUnwind {
        dropped_place,
        block,
    } = handle_result!(syn::parse2(tokens));
    ghost_with_annotation(
        quote! { #block },
        unsafe_spec_function_call(quote! {
            prusti_on_drop_unwind(std::ptr::addr_of!(#dropped_place))
        }),
        false,
        quote! {specification_region_begin},
        quote! {specification_region_end},
        None,
    )
}

pub fn with_finally(tokens: TokenStream) -> TokenStream {
    let WithFinally {
        executed_block,
        on_panic_block,
        finally_block,
    } = handle_result!(syn::parse2(tokens));
    let mut rewriter = rewriter::AstRewriter::new();
    let on_panic_spec_id = rewriter.generate_spec_id();
    let on_panic_spec_id_str = on_panic_spec_id.to_string();
    let finally_spec_id = rewriter.generate_spec_id();
    let finally_spec_id_str = finally_spec_id.to_string();
    let make_closure = |kind| {
        quote! {
            #[allow(unused_must_use, unused_variables, unused_braces, unused_parens)]
            if false {
                #[prusti::spec_only]
                #[prusti::#kind]
                #[prusti::on_panic_spec_id = #on_panic_spec_id_str]
                #[prusti::finally_spec_id = #finally_spec_id_str]
                || -> () {};
            }
        }
    };
    let executed_block_begin = make_closure(quote! {try_finally_executed_block_begin});
    let executed_block_end = make_closure(quote! {try_finally_executed_block_end});
    let on_panic_ghost_block = ghost_with_annotation(
        quote! { #on_panic_block },
        quote! {},
        false,
        quote! {specification_region_begin},
        quote! {specification_region_end},
        Some(on_panic_spec_id),
    );
    let finally_ghost_block = ghost_with_annotation(
        quote! { #finally_block },
        quote! {},
        false,
        quote! {specification_region_begin},
        quote! {specification_region_end},
        Some(finally_spec_id),
    );
    quote! {
        #executed_block_begin
        #(#executed_block)*
        #executed_block_end
        #on_panic_ghost_block
        #finally_ghost_block
    }
}

pub fn checked(tokens: TokenStream) -> TokenStream {
    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id = rewriter.generate_spec_id();
    let spec_id_str = spec_id.to_string();
    let make_closure = |kind| {
        quote! {
            #[allow(unused_must_use, unused_variables, unused_braces, unused_parens)]
            if false {
                #[prusti::spec_only]
                #[prusti::#kind]
                #[prusti::spec_id = #spec_id_str]
                || -> () {};
            }
        }
    };
    let checked_block_begin = make_closure(quote! {checked_block_begin});
    let checked_block_end = make_closure(quote! {checked_block_end});
    let tokens = quote! {
        {
            #checked_block_begin
            let result = { #tokens };
            #checked_block_end
            result
        }
    };
    tokens
}

pub fn manually_manage(tokens: TokenStream) -> TokenStream {
    generate_place_function(tokens, quote! {prusti_manually_manage})
}

pub fn pack(tokens: TokenStream) -> TokenStream {
    generate_place_function(tokens, quote! {prusti_pack_place})
}

pub fn unpack(tokens: TokenStream) -> TokenStream {
    generate_place_function(tokens, quote! {prusti_unpack_place})
}

pub fn obtain(tokens: TokenStream) -> TokenStream {
    generate_place_function(tokens, quote! {prusti_obtain_place})
}

pub fn pack_ref(tokens: TokenStream) -> TokenStream {
    // generate_place_function(tokens, quote! {prusti_pack_ref_place})
    pack_unpack_ref(tokens, quote! {prusti_pack_ref_place})
}

pub fn unpack_ref(tokens: TokenStream) -> TokenStream {
    // generate_place_function(tokens, quote! {prusti_unpack_ref_place})
    pack_unpack_ref(tokens, quote! {prusti_unpack_ref_place})
}

pub fn pack_mut_ref(tokens: TokenStream) -> TokenStream {
    // generate_place_function(tokens, quote! {prusti_pack_mut_ref_place})
    pack_unpack_ref(tokens, quote! {prusti_pack_mut_ref_place})
}

pub fn unpack_mut_ref(tokens: TokenStream) -> TokenStream {
    // // generate_place_function(tokens, quote!{prusti_unpack_mut_ref_place})
    // let (lifetime_name, reference) =
    //     handle_result!(parse_two_expressions::<syn::Token![,]>(tokens));
    // let lifetime_name_str = handle_result!(expression_to_string(&lifetime_name));
    // unsafe_spec_function_call(quote! {`
    //     prusti_unpack_mut_ref_place(#lifetime_name_str, std::ptr::addr_of!(#reference))
    // })
    pack_unpack_ref(tokens, quote! {prusti_unpack_mut_ref_place})
}

fn pack_unpack_ref(tokens: TokenStream, function: TokenStream) -> TokenStream {
    // let (lifetime_name, reference) =
    //     handle_result!(parse_two_expressions::<syn::Token![,]>(tokens));
    parse_expressions!(tokens, syn::Token![,] => lifetime_name, reference);
    let lifetime_name_str = handle_result!(expression_to_string(&lifetime_name));
    unsafe_spec_function_call(quote! {
        #function(#lifetime_name_str, std::ptr::addr_of!(#reference))
    })
}

// fn parse_two_expressions<Separator: syn::parse::Parse>(
//     tokens: TokenStream,
// ) -> syn::Result<(syn::Expr, syn::Expr)> {
//     // let parser = syn::punctuated::Punctuated::<syn::Expr, Separator>::parse_terminated;
//     // let mut expressions = syn::parse::Parser::parse2(parser, tokens)?;
//     // let second = expressions
//     //     .pop()
//     //     .ok_or_else(|| syn::Error::new(Span::call_site(), "Expected two expressions"))?;
//     // let first = expressions
//     //     .pop()
//     //     .ok_or_else(|| syn::Error::new(Span::call_site(), "Expected two expressions"))?;
//     // Ok((first.into_value(), second.into_value()))
//     parse_expressions!(tokens, Separator => first, second);
//     Ok((first, second))
// }

// fn parse_three_expressions<Separator: syn::parse::Parse>(
//     tokens: TokenStream,
// ) -> syn::Result<(syn::Expr, syn::Expr, syn::Expr)> {
//     // let parser = syn::punctuated::Punctuated::<syn::Expr, Separator>::parse_terminated;
//     // let mut expressions = syn::parse::Parser::parse2(parser, tokens)?;
//     // let third = expressions
//     //     .pop()
//     //     .ok_or_else(|| syn::Error::new(Span::call_site(), "Expected three expressions"))?;
//     // let second = expressions
//     //     .pop()
//     //     .ok_or_else(|| syn::Error::new(Span::call_site(), "Expected three expressions"))?;
//     // let first = expressions
//     //     .pop()
//     //     .ok_or_else(|| syn::Error::new(Span::call_site(), "Expected three expressions"))?;
//     // Ok((first.into_value(), second.into_value(), third.into_value()))
//     parse_expressions!(tokens, Separator => first, second, third);
//     Ok((first, second, third))
// }

// fn parse_four_expressions<Separator: syn::parse::Parse>(
//     tokens: TokenStream,
// ) -> syn::Result<(syn::Expr, syn::Expr, syn::Expr, syn::Expr)> {
//     // let parser = syn::punctuated::Punctuated::<syn::Expr, Separator>::parse_terminated;
//     // let mut expressions = syn::parse::Parser::parse2(parser, tokens)?;
//     // let fourth = expressions
//     //     .pop()
//     //     .ok_or_else(|| syn::Error::new(Span::call_site(), "Expected four expressions"))?;
//     // let third = expressions
//     //     .pop()
//     //     .ok_or_else(|| syn::Error::new(Span::call_site(), "Expected four expressions"))?;
//     // let second = expressions
//     //     .pop()
//     //     .ok_or_else(|| syn::Error::new(Span::call_site(), "Expected four expressions"))?;
//     // let first = expressions
//     //     .pop()
//     //     .ok_or_else(|| syn::Error::new(Span::call_site(), "Expected four expressions"))?;
//     // Ok((
//     //     first.into_value(),
//     //     second.into_value(),
//     //     third.into_value(),
//     //     fourth.into_value(),
//     // ))
//     parse_expressions!(tokens, Separator => first, second, third, fourth);
//     Ok((first, second, third, fourth))
// }

fn expression_to_string(expr: &syn::Expr) -> syn::Result<String> {
    if let syn::Expr::Path(syn::ExprPath {
        qself: None, path, ..
    }) = expr
    {
        if let Some(ident) = path.get_ident() {
            return Ok(ident.to_string());
        }
    }
    Err(syn::Error::new(expr.span(), "needs to be an identifier"))
}

pub fn unsafe_spec_function_call(call: TokenStream) -> TokenStream {
    let callsite_span = Span::call_site();
    quote_spanned! { callsite_span =>
        #[allow(unused_must_use, unused_variables)]
        #[prusti::specs_version = #SPECS_VERSION]
        if false {
            #[prusti::spec_only]
            || -> bool { true };
            unsafe { #call };
        }
    }
}

pub fn take_lifetime(tokens: TokenStream) -> TokenStream {
    parse_expressions!(tokens, syn::Token![,] => reference, lifetime_name);
    // let (reference, lifetime_name) =
    //     handle_result!(parse_two_expressions::<syn::Token![,]>(tokens));
    let lifetime_name_str = handle_result!(expression_to_string(&lifetime_name));
    unsafe_spec_function_call(quote! {
        prusti_take_lifetime(std::ptr::addr_of!(#reference), #lifetime_name_str)
    })
    // let parser = syn::punctuated::Punctuated::<syn::Expr, syn::Token![=>]>::parse_terminated;
    // let mut args = handle_result!(syn::parse::Parser::parse2(parser, tokens));
    // let lifetime = if let Some(lifetime) = args.pop() {
    //     lifetime.into_value()
    // } else {
    //     return syn::Error::new(
    //         args.span(),
    //         "`take_lifetime!` needs to contain two arguments `<reference>` and `<lifetime name>`"
    //     ).to_compile_error();
    // };
    // let lifetime_str = if let syn::Expr::Path(syn::ExprPath { qself: None, path, ..}) = lifetime {
    //     if let Some(ident) = path.get_ident() {
    //         ident.to_string()
    //     } else {
    //         return syn::Error::new(
    //             path.span(),
    //             "lifetime name needs to be an identifier"
    //         ).to_compile_error();
    //     }
    // } else {
    //     return syn::Error::new(
    //         lifetime.span(),
    //         "lifetime name needs to be an identifier"
    //     ).to_compile_error();
    // };
    // let reference = if let Some(reference) = args.pop() {
    //     reference.into_value()
    // } else {
    //     return syn::Error::new(
    //         args.span(),
    //         "`take_lifetime!` needs to contain two arguments `<reference>` and `<lifetime name>`"
    //     ).to_compile_error();
    // };
    // let callsite_span = Span::call_site();
    // quote_spanned! { callsite_span =>
    //     #[allow(unused_must_use, unused_variables)]
    //     #[prusti::specs_version = #SPECS_VERSION]
    //     if false {
    //         #[prusti::spec_only]
    //         || -> bool { true };
    //         unsafe { prusti_take_lifetime(std::ptr::addr_of!(#reference), #lifetime_str) };
    //     }
    // }
}

pub fn set_lifetime_for_raw_pointer_reference_casts(tokens: TokenStream) -> TokenStream {
    unsafe_spec_function_call(quote! {
        prusti_set_lifetime_for_raw_pointer_reference_casts(std::ptr::addr_of!(#tokens))
    })
}

pub fn join(tokens: TokenStream) -> TokenStream {
    generate_place_function(tokens, quote! {prusti_join_place})
}

pub fn join_range(tokens: TokenStream) -> TokenStream {
    parse_expressions!(tokens, syn::Token![,] => pointer, start_index, end_index);
    // let (pointer, start_index, end_index) =
    //     handle_result!(parse_three_expressions::<syn::Token![,]>(tokens));
    unsafe_spec_function_call(quote! {
        prusti_join_range(std::ptr::addr_of!(#pointer), {#start_index}, #end_index)
    })
}

pub fn split(tokens: TokenStream) -> TokenStream {
    generate_place_function(tokens, quote! {prusti_split_place})
}

pub fn split_range(tokens: TokenStream) -> TokenStream {
    parse_expressions!(tokens, syn::Token![,] => pointer, start_index, end_index);
    // let (pointer, start_index, end_index) =
    //     handle_result!(parse_three_expressions::<syn::Token![,]>(tokens));
    unsafe_spec_function_call(quote! {
        prusti_split_range(std::ptr::addr_of!(#pointer), {#start_index}, #end_index)
    })
}

/// FIXME: For `start_index` and `end_index`, we should do the same as for
/// `body_invariant!`.
pub fn stash_range(tokens: TokenStream) -> TokenStream {
    parse_expressions!(tokens, syn::Token![,] => pointer, start_index, end_index, witness);
    // let (pointer, start_index, end_index, witness) =
    //     handle_result!(parse_four_expressions::<syn::Token![,]>(tokens));
    let witness_str = handle_result!(expression_to_string(&witness));
    unsafe_spec_function_call(quote! {
        prusti_stash_range(
            std::ptr::addr_of!(#pointer),
            {#start_index},
            {#end_index},
            #witness_str
        )
    })
}

/// FIXME: For `new_start_index`, we should do the same as for
/// `body_invariant!`.
pub fn restore_stash_range(tokens: TokenStream) -> TokenStream {
    parse_expressions!(tokens, syn::Token![,] => pointer, new_start_index, witness);
    // let (pointer, new_start_index, witness) =
    //     handle_result!(parse_three_expressions::<syn::Token![,]>(tokens));
    let witness_str = handle_result!(expression_to_string(&witness));
    unsafe_spec_function_call(quote! {
        prusti_restore_stash_range(std::ptr::addr_of!(#pointer), {#new_start_index}, #witness_str)
    })
}

pub fn materialize_predicate(tokens: TokenStream) -> TokenStream {
    let (spec_id, predicate_closure) = handle_result!(prusti_specification_expression(tokens));
    let spec_id_str = spec_id.to_string();
    let call = unsafe_spec_function_call(quote! { prusti_materialize_predicate(#spec_id_str) });
    quote! {
        #call;
        #predicate_closure
    }
}

pub fn quantified_predicate(tokens: TokenStream) -> TokenStream {
    let (spec_id, predicate_closure) = handle_result!(prusti_specification_expression(tokens));
    let spec_id_str = spec_id.to_string();
    let call = unsafe_spec_function_call(quote! { prusti_quantified_predicate(#spec_id_str) });
    quote! {
        #call;
        #predicate_closure
    }
}

fn close_any_ref(tokens: TokenStream, function: TokenStream) -> TokenStream {
    parse_expressions!(tokens, syn::Token![,] => reference, witness);
    // let (reference, witness) = handle_result!(parse_two_expressions::<syn::Token![,]>(tokens));
    let witness_str = handle_result!(expression_to_string(&witness));
    let (spec_id, reference_closure) = handle_result!(prusti_specification_expression(
        quote! { unsafe { &#reference } }
    ));
    let spec_id_str = spec_id.to_string();
    let call = unsafe_spec_function_call(quote! { #function(#spec_id_str, #witness_str) });
    quote! {
        #call;
        #reference_closure
    }
}

pub fn close_ref(tokens: TokenStream) -> TokenStream {
    close_any_ref(tokens, quote! {prusti_close_ref_place})
}

pub fn close_mut_ref(tokens: TokenStream) -> TokenStream {
    close_any_ref(tokens, quote! {prusti_close_mut_ref_place})
}

fn open_any_ref(tokens: TokenStream, function: TokenStream) -> TokenStream {
    parse_expressions!(tokens, syn::Token![,] => lifetime_name, reference, witness);
    // let (lifetime_name, reference, witness) =
    //     handle_result!(parse_three_expressions::<syn::Token![,]>(tokens));
    let lifetime_name_str = handle_result!(expression_to_string(&lifetime_name));
    let witness_str = handle_result!(expression_to_string(&witness));
    let (spec_id, reference_closure) = handle_result!(prusti_specification_expression(
        quote! { unsafe { &#reference } }
    ));
    let spec_id_str = spec_id.to_string();
    let call = unsafe_spec_function_call(quote! {
        #function(#lifetime_name_str, #spec_id_str, #witness_str)
    });
    quote! {
        #reference_closure;
        #call
    }
}

pub fn open_ref(tokens: TokenStream) -> TokenStream {
    open_any_ref(tokens, quote! {prusti_open_ref_place})
}

pub fn open_mut_ref(tokens: TokenStream) -> TokenStream {
    open_any_ref(tokens, quote! {prusti_open_mut_ref_place})
}

pub fn resolve(tokens: TokenStream) -> TokenStream {
    generate_place_function(tokens, quote! {prusti_resolve})
}

pub fn resolve_range(tokens: TokenStream) -> TokenStream {
    parse_expressions!(tokens, syn::Token![,] =>
        lifetime_name,
        pointer,
        predicate_range_start_index,
        predicate_range_end_index,
        start_index,
        end_index
    );
    // let (lifetime_name, pointer, base_index, start_index, end_index) =
    //     handle_result!(parse_five_expressions::<syn::Token![,]>(tokens));
    let lifetime_name_str = handle_result!(expression_to_string(&lifetime_name));
    unsafe_spec_function_call(quote! {
        prusti_resolve_range(
            #lifetime_name_str,
            std::ptr::addr_of!(#pointer),
            {#predicate_range_start_index},
            {#predicate_range_end_index},
            {#start_index},
            {#end_index},
        )
    })
}

pub fn set_union_active_field(tokens: TokenStream) -> TokenStream {
    generate_place_function(tokens, quote! {prusti_set_union_active_field})
}

pub fn forget_initialization(tokens: TokenStream) -> TokenStream {
    generate_place_function(tokens, quote! {prusti_forget_initialization})
}

pub fn forget_initialization_range(tokens: TokenStream) -> TokenStream {
    parse_expressions!(tokens, syn::Token![,] => pointer, start_index, end_index);
    unsafe_spec_function_call(quote! {
        prusti_forget_initialization_range(
            std::ptr::addr_of!(#pointer),
            {#start_index},
            {#end_index},
        )
    })
}

fn generate_place_function(tokens: TokenStream, function: TokenStream) -> TokenStream {
    let callsite_span = Span::call_site();
    quote_spanned! { callsite_span =>
        #[allow(unused_must_use, unused_variables)]
        #[prusti::specs_version = #SPECS_VERSION]
        if false {
            #[prusti::spec_only]
            || -> bool { true };
            unsafe { #function(std::ptr::addr_of!(#tokens)) };
        }
    }
}

pub fn restore(tokens: TokenStream) -> TokenStream {
    let parser = syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated;
    let mut args = handle_result!(syn::parse::Parser::parse2(parser, tokens));
    let restored_place = if let Some(restored_place) = args.pop() {
        restored_place.into_value()
    } else {
        return syn::Error::new(
            args.span(),
            "`restore!` needs to contain two arguments `<borrowing place>` and `<place to restore>`"
        ).to_compile_error();
    };
    let borrowing_place = if let Some(borrowing_place) = args.pop() {
        borrowing_place.into_value()
    } else {
        return syn::Error::new(
            args.span(),
            "`restore!` needs to contain two arguments `<borrowing place>` and `<place to restore>`"
        ).to_compile_error();
    };
    let callsite_span = Span::call_site();
    quote_spanned! { callsite_span =>
        #[allow(unused_must_use, unused_variables)]
        #[prusti::specs_version = #SPECS_VERSION]
        if false {
            #[prusti::spec_only]
            || -> bool { true };
            unsafe { prusti_restore_place(std::ptr::addr_of!(#borrowing_place), std::ptr::addr_of!(#restored_place)) };
        }
    }
}
