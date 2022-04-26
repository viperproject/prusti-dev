#![deny(unused_must_use)]
#![feature(drain_filter)]
#![feature(box_patterns)]
#![feature(box_syntax)]
#![feature(if_let_guard)]
// This Clippy chcek seems to be always wrong.
#![allow(clippy::iter_with_drain)]

#[macro_use]
mod common;
mod parse_quote_spanned;
mod span_overrider;
mod extern_spec_rewriter;
mod rewriter;
mod parse_closure_macro;
mod predicate;
mod spec_attribute_kind;
mod ghost_constraints;
mod type_model;
mod user_provided_type_params;
pub mod specifications;

use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{quote_spanned, ToTokens};
use syn::spanned::Spanned;
use std::convert::TryInto;

use specifications::common::SpecificationId;
use specifications::untyped;
use parse_closure_macro::ClosureWithSpec;
pub use spec_attribute_kind::SpecAttributeKind;
use prusti_utils::force_matches;
pub use extern_spec_rewriter::ExternSpecKind;
use crate::common::{merge_generics, RewritableReceiver, SelfTypeRewriter};
use crate::specifications::preparser::{NestedSpec, parse_ghost_constraint};
use crate::predicate::{is_predicate_macro, ParsedPredicate};

macro_rules! handle_result {
    ($parse_result: expr) => {
        match $parse_result {
            Ok(data) => data,
            Err(err) => return err.to_compile_error(),
        }
    };
}

fn extract_prusti_attributes(
    item: &mut untyped::AnyFnItem
) -> Vec<(SpecAttributeKind, TokenStream)> {
    let mut prusti_attributes = Vec::new();
    let mut regular_attributes = Vec::new();
    for attr in item.attrs_mut().drain(0..) {
        if attr.path.segments.len() == 1 {
            if let Ok(attr_kind) = attr.path.segments[0].ident.to_string().try_into() {
                let tokens = match attr_kind {
                    SpecAttributeKind::Requires
                    | SpecAttributeKind::Ensures
                    | SpecAttributeKind::AfterExpiry
                    | SpecAttributeKind::AssertOnExpiry
                    | SpecAttributeKind::GhostConstraint => {
                        // We need to drop the surrounding parenthesis to make the
                        // tokens identical to the ones passed by the native procedural
                        // macro call.
                        let mut iter = attr.tokens.into_iter();
                        let tokens = force_matches!(iter.next().unwrap(), TokenTree::Group(group) => group.stream());
                        assert!(iter.next().is_none(), "Unexpected shape of an attribute.");
                        tokens
                    }
                    // Nothing to do for attributes without arguments.
                    SpecAttributeKind::Pure
                    | SpecAttributeKind::Trusted
                    | SpecAttributeKind::Predicate => {
                        assert!(attr.tokens.is_empty(), "Unexpected shape of an attribute.");
                        attr.tokens
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
    let mut prusti_attributes = vec![
        (outer_attr_kind, outer_attr_tokens)
    ];

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
        ).to_compile_error();
    }

    let (generated_spec_items, generated_attributes) = handle_result!(
        generate_spec_and_assertions(prusti_attributes, &item)
    );

    quote_spanned! {item.span()=>
        #(#generated_spec_items)*
        #(#generated_attributes)*
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
            SpecAttributeKind::AfterExpiry => generate_for_after_expiry(attr_tokens, item),
            SpecAttributeKind::AssertOnExpiry => generate_for_assert_on_expiry(attr_tokens, item),
            SpecAttributeKind::Pure => generate_for_pure(attr_tokens, item),
            SpecAttributeKind::Trusted => generate_for_trusted(attr_tokens, item),
            // Predicates are handled separately below; the entry in the SpecAttributeKind enum
            // only exists so we successfully parse it and emit an error in
            // `check_incompatible_attrs`; so we'll never reach here.
            SpecAttributeKind::Predicate => unreachable!(),
            SpecAttributeKind::GhostConstraint => ghost_constraints::generate(attr_tokens, item),
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
    let spec_item = rewriter.process_assertion(
        rewriter::SpecItemType::Precondition,
        spec_id,
        attr,
        item,
    )?;
    Ok((
        vec![spec_item],
        vec![parse_quote_spanned! {item.span()=>
            #[prusti::pre_spec_id_ref = #spec_id_str]
        }],
    ))
}

/// Generate spec items and attributes to typecheck the and later retrieve "ensures" annotations.
fn generate_for_ensures(attr: TokenStream, item: &untyped::AnyFnItem) -> GeneratedResult {
    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id = rewriter.generate_spec_id();
    let spec_id_str = spec_id.to_string();
    let spec_item = rewriter.process_assertion(
        rewriter::SpecItemType::Postcondition,
        spec_id,
        attr,
        item,
    )?;
    Ok((
        vec![spec_item],
        vec![parse_quote_spanned! {item.span()=>
            #[prusti::post_spec_id_ref = #spec_id_str]
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
    let (spec_item_lhs, spec_item_rhs) = rewriter.process_assert_pledge(spec_id_lhs, spec_id_rhs, attr, item)?;
    Ok((
        vec![spec_item_lhs, spec_item_rhs],
        vec![parse_quote_spanned! {item.span()=>
            #[prusti::assert_pledge_spec_id_ref_lhs = #spec_id_lhs_str]
        },
        parse_quote_spanned! {item.span()=>
            #[prusti::assert_pledge_spec_id_ref_rhs = #spec_id_rhs_str]
        }],
    ))
}

/// Generate spec items and attributes to typecheck and later retrieve "pure" annotations.
fn generate_for_pure(attr: TokenStream, item: &untyped::AnyFnItem) -> GeneratedResult {
    if !attr.is_empty() {
        return Err(syn::Error::new(
            attr.span(),
            "the `#[pure]` attribute does not take parameters"
        ));
    }

    Ok((
        vec![],
        vec![parse_quote_spanned! {item.span()=>
            #[prusti::pure]
        }],
    ))
}

/// Generate spec items and attributes to typecheck and later retrieve "trusted" annotations.
fn generate_for_trusted(attr: TokenStream, item: &untyped::AnyFnItem) -> GeneratedResult {
    if !attr.is_empty() {
        return Err(syn::Error::new(
            attr.span(),
            "the `#[trusted]` attribute does not take parameters"
        ));
    }

    Ok((
        vec![],
        vec![parse_quote_spanned! {item.span()=>
            #[prusti::trusted]
        }],
    ))
}

pub fn body_invariant(tokens: TokenStream) -> TokenStream {
    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id = rewriter.generate_spec_id();
    let invariant = handle_result!(rewriter.process_loop_invariant(spec_id, tokens));
    let callsite_span = Span::call_site();
    quote_spanned! {callsite_span=>
        #[allow(unused_must_use, unused_variables)]
        if false {
            #invariant
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
    let cl_spec: ClosureWithSpec = handle_result!(syn::parse(tokens.into()));
    let callsite_span = Span::call_site();

    if drop_spec {
        return cl_spec.cl.into_token_stream()
    }

    let mut rewriter = rewriter::AstRewriter::new();

    let mut preconds: Vec<(SpecificationId, syn::Expr)> = vec![];
    let mut postconds: Vec<(SpecificationId, syn::Expr)> = vec![];

    let mut cl_annotations = TokenStream::new();

    for r in cl_spec.pres {
        let spec_id = rewriter.generate_spec_id();
        let precond = handle_result!(rewriter.process_closure_assertion(
            spec_id,
            r.to_token_stream(),
        ));
        preconds.push((spec_id, precond));
        let spec_id_str = spec_id.to_string();
        cl_annotations.extend(quote_spanned! {callsite_span=>
            #[prusti::pre_spec_id_ref = #spec_id_str]
        });
    }

    for e in cl_spec.posts {
        let spec_id = rewriter.generate_spec_id();
        let postcond = handle_result!(rewriter.process_closure_assertion(
            spec_id,
            e.to_token_stream(),
        ));
        postconds.push((spec_id, postcond));
        let spec_id_str = spec_id.to_string();
        cl_annotations.extend(quote_spanned! {callsite_span=>
            #[prusti::post_spec_id_ref = #spec_id_str]
        });
    }

    let syn::ExprClosure {
        attrs, asyncness, movability, capture, or1_token,
        inputs, or2_token, output, body
    } = cl_spec.cl;

    let output_type: syn::Type = match output {
        syn::ReturnType::Default => {
            return syn::Error::new(output.span(), "closure must specify return type")
                .to_compile_error();
        }
        syn::ReturnType::Type(_, ref ty) => (**ty).clone()
    };

    let (spec_toks_pre, spec_toks_post) = handle_result!(rewriter.process_closure(
        inputs.clone(),
        output_type,
        preconds,
        postconds,
    ));

    let mut attrs_ts = TokenStream::new();
    for a in attrs {
        attrs_ts.extend(a.into_token_stream());
    }

    quote_spanned! {callsite_span=>
        {
            #[allow(unused_variables)]
            #[prusti::closure]
            #cl_annotations #attrs_ts
            let _prusti_closure =
                #asyncness #movability #capture
                #or1_token #inputs #or2_token #output
                {
                    #[allow(unused_must_use)]
                    if false {
                        #spec_toks_pre
                    }
                    let result = #body ;
                    #[allow(unused_must_use)]
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
        None => handle_result!(Err(syn::Error::new(impl_block.span(), "Can refine trait specifications only on trait implementation blocks"))),
    };

    let self_type_path: &syn::TypePath = match &*impl_block.self_ty {
        syn::Type::Path(type_path) => type_path,
        _ => unimplemented!("Currently not supported: {:?}", impl_block.self_ty),
    };

    let mut new_items = Vec::new();
    let mut generated_spec_items = Vec::new();
    for item in impl_block.items {
        match item {
            syn::ImplItem::Method(method) => {
                let mut method_item = untyped::AnyFnItem::ImplMethod(method);
                let prusti_attributes: Vec<_> = extract_prusti_attributes(&mut method_item);

                let illegal_attribute_span = prusti_attributes.iter()
                    .filter(|(kind, _)| kind == &SpecAttributeKind::GhostConstraint)
                    .map(|(_, tokens)| tokens.span())
                    .next();
                if let Some(span) = illegal_attribute_span {
                    let err = Err(syn::Error::new(span, "Ghost constraints in trait spec refinements not supported"));
                    handle_result!(err);
                }

                let (spec_items, generated_attributes) = handle_result!(
                    generate_spec_and_assertions(prusti_attributes, &method_item)
                );

                spec_items.into_iter()
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
            },
            syn::ImplItem::Macro(makro) if is_predicate_macro(&makro) => {
                let parsed_predicate = handle_result!(predicate::parse_predicate_in_impl(makro.mac.tokens.clone()));

                let predicate = force_matches!(parsed_predicate, ParsedPredicate::Impl(p) => p);

                // Patch spec function: Rewrite self with _self: <SpecStruct>
                let spec_function = force_matches!(predicate.spec_function,
                    syn::Item::Fn(item_fn) => item_fn);
                generated_spec_items.push(spec_function);

                // Add patched predicate function to new items
                new_items.push(syn::ImplItem::Method(predicate.patched_function));
            },
            _ => new_items.push(item),
        }
    }

    // Patch the spec items (merge generics, handle associated types, rewrite receiver)
    for generated_spec_item in generated_spec_items.iter_mut() {
        merge_generics(&mut generated_spec_item.sig.generics, impl_generics);
        generated_spec_item.rewrite_self_type(self_type_path, Some(&trait_path));
        generated_spec_item.rewrite_receiver(self_type_path);
    }

    impl_block.items = new_items;
    quote_spanned! {impl_block.span()=>
        #(#generated_spec_items)*
        #impl_block
    }
}

pub fn extern_spec(_attr: TokenStream, tokens:TokenStream) -> TokenStream {
    let item: syn::Item = handle_result!(syn::parse2(tokens));
    match item {
        syn::Item::Impl(item_impl) => {
            handle_result!(extern_spec_rewriter::impls::rewrite_extern_spec(&item_impl))
        }
        syn::Item::Trait(item_trait) => {
            handle_result!(extern_spec_rewriter::traits::rewrite_extern_spec(&item_trait))
        }
        syn::Item::Mod(mut item_mod) => {
            handle_result!(extern_spec_rewriter::mods::rewrite_extern_spec(&mut item_mod))
        }
        _ => { unimplemented!() }
    }
}

pub fn predicate(tokens: TokenStream) -> TokenStream {
    let parsed = handle_result!(predicate::parse_predicate(tokens));
    parsed.into_token_stream()
}

pub fn type_model(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    let item: syn::Item = handle_result!(syn::parse2(tokens));

    match item {
        syn::Item::Struct(item_struct) => {
            handle_result!(type_model::rewrite(item_struct))
        }
        _ => {
            unimplemented!("Only structs can be attributed with 'model'")
        }
    }
}