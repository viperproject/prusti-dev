#![deny(unused_must_use)]
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
mod predicate;
mod rewriter;
mod span_overrider;
mod spec_attribute_kind;
pub mod specifications;
mod type_model;
mod user_provided_type_params;
mod print_counterexample;

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

/// The argument of an attribute in inner position, i.e. its tokens with the
/// surrounding parenthesis dropped. This makes them identical to the ones
/// passed by the native procedural macro call.
fn unwrap_argument(tokens: TokenStream) -> TokenStream {
    let mut iter = tokens.into_iter();
    let Some(TokenTree::Group(group)) = iter.next() else {
        unreachable!("Unexpected shape of an attribute.")
    };
    assert!(iter.next().is_none(), "Unexpected shape of an attribute.");
    group.stream()
}

fn extract_prusti_attributes(
    item: &mut untyped::AnyFnItem,
) -> Vec<(SpecAttributeKind, Span, TokenStream)> {
    let mut prusti_attributes = Vec::new();
    let mut regular_attributes = Vec::new();
    for attr in item.attrs_mut().drain(0..) {
        if attr.path.segments.len() == 1
            || (attr.path.segments.len() == 2 && attr.path.segments[0].ident == "prusti_contracts")
        {
            let idx = attr.path.segments.len() - 1;
            if let Ok(attr_kind) = attr.path.segments[idx].ident.to_string().try_into() {
                // The span of the annotation itself, so diagnostics can point
                // at the specific attribute rather than the whole item.
                let attr_span = attr.path.span();
                let tokens = match attr_kind {
                    SpecAttributeKind::Requires
                    | SpecAttributeKind::Ensures
                    | SpecAttributeKind::AfterExpiry
                    | SpecAttributeKind::AssertOnExpiry
                    | SpecAttributeKind::RefineSpec => unwrap_argument(attr.tokens),
                    // The argument of `terminates` is optional.
                    SpecAttributeKind::Terminates if !attr.tokens.is_empty() => {
                        unwrap_argument(attr.tokens)
                    }
                    // Nothing to do for attributes without arguments.
                    SpecAttributeKind::Pure
                    | SpecAttributeKind::Terminates
                    | SpecAttributeKind::Trusted
                    | SpecAttributeKind::Predicate
                    | SpecAttributeKind::Verified => {
                        assert!(attr.tokens.is_empty(), "Unexpected shape of an attribute.");
                        attr.tokens
                    }
                    SpecAttributeKind::Invariant => unreachable!("type invariant on function"),
                    SpecAttributeKind::Model => unreachable!("model on function"),
                    SpecAttributeKind::PrintCounterexample => {
                        unreachable!("print_counterexample on function")
                    }
                };
                prusti_attributes.push((attr_kind, attr_span, tokens));
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

    // Start with the outer attribute. It is the one the compiler ran as the
    // procedural macro, so its span is the call site.
    let mut prusti_attributes = vec![(outer_attr_kind, Span::call_site(), outer_attr_tokens)];

    // Collect the remaining Prusti attributes, removing them from `item`.
    prusti_attributes.extend(extract_prusti_attributes(&mut item));

    // make sure to also update the check in the predicate! handling method
    if prusti_attributes
        .iter()
        .any(|(ak, _, _)| ak == &SpecAttributeKind::Predicate)
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
    mut prusti_attributes: Vec<(SpecAttributeKind, Span, TokenStream)>,
    item: &untyped::AnyFnItem,
) -> GeneratedResult {
    let mut generated_items = vec![];
    let mut generated_attributes = vec![];

    for (attr_kind, attr_span, attr_tokens) in prusti_attributes.drain(..) {
        let rewriting_result = match attr_kind {
            SpecAttributeKind::Requires => generate_for_requires(attr_tokens, attr_span, item),
            SpecAttributeKind::Ensures => generate_for_ensures(attr_tokens, attr_span, item),
            SpecAttributeKind::AfterExpiry => {
                generate_for_after_expiry(attr_tokens, attr_span, item)
            }
            SpecAttributeKind::AssertOnExpiry => {
                generate_for_assert_on_expiry(attr_tokens, attr_span, item)
            }
            SpecAttributeKind::Pure => generate_for_pure(attr_tokens, attr_span, item),
            SpecAttributeKind::Verified => generate_for_verified(attr_tokens, attr_span, item),
            SpecAttributeKind::Terminates => generate_for_terminates(attr_tokens, attr_span, item),
            SpecAttributeKind::Trusted => generate_for_trusted(attr_tokens, attr_span, item),
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
fn generate_for_requires(
    attr: TokenStream,
    span: Span,
    item: &untyped::AnyFnItem,
) -> GeneratedResult {
    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id = rewriter.generate_spec_id();
    let spec_id_str = spec_id.to_string();
    let spec_item =
        rewriter.process_assertion(rewriter::SpecItemType::Precondition, spec_id, attr, item)?;
    Ok((
        vec![spec_item],
        vec![parse_quote_spanned! {span=>
            #[prusti::pre_spec_id_ref = #spec_id_str]
        }],
    ))
}

/// Generate spec items and attributes to typecheck the and later retrieve "ensures" annotations.
fn generate_for_ensures(
    attr: TokenStream,
    span: Span,
    item: &untyped::AnyFnItem,
) -> GeneratedResult {
    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id = rewriter.generate_spec_id();
    let spec_id_str = spec_id.to_string();
    let spec_item =
        rewriter.process_assertion(rewriter::SpecItemType::Postcondition, spec_id, attr, item)?;
    Ok((
        vec![spec_item],
        vec![parse_quote_spanned! {span=>
            #[prusti::post_spec_id_ref = #spec_id_str]
        }],
    ))
}

/// Generate spec items and attributes to typecheck and later retrieve "after_expiry" annotations.
fn generate_for_after_expiry(
    attr: TokenStream,
    span: Span,
    item: &untyped::AnyFnItem,
) -> GeneratedResult {
    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id = rewriter.generate_spec_id();
    let spec_id_str = spec_id.to_string();
    let spec_item = rewriter.process_pledge(spec_id, attr, item)?;
    Ok((
        vec![spec_item],
        vec![parse_quote_spanned! {span=>
            #[prusti::pledge_spec_id_ref = #spec_id_str]
        }],
    ))
}

/// Generate spec items and attributes to typecheck and later retrieve "after_expiry" annotations.
fn generate_for_assert_on_expiry(
    attr: TokenStream,
    span: Span,
    item: &untyped::AnyFnItem,
) -> GeneratedResult {
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
            parse_quote_spanned! {span=>
                #[prusti::assert_pledge_spec_id_ref_lhs = #spec_id_lhs_str]
            },
            parse_quote_spanned! {span=>
                #[prusti::assert_pledge_spec_id_ref_rhs = #spec_id_rhs_str]
            },
        ],
    ))
}

/// Generate spec items and attributes to typecheck and later retrieve "terminates" annotations.
fn generate_for_terminates(
    mut attr: TokenStream,
    span: Span,
    item: &untyped::AnyFnItem,
) -> GeneratedResult {
    if attr.is_empty() {
        attr = quote! { Int::from(1) };
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
        vec![parse_quote_spanned! {span=>
            #[prusti::terminates_spec_id_ref = #spec_id_str]
        }],
    ))
}

/// Generate spec items and attributes to typecheck and later retrieve "pure" annotations.
fn generate_for_pure(attr: TokenStream, span: Span, _item: &untyped::AnyFnItem) -> GeneratedResult {
    if !attr.is_empty() {
        return Err(syn::Error::new(
            attr.span(),
            "the `#[pure]` attribute does not take parameters",
        ));
    }

    Ok((
        vec![],
        vec![parse_quote_spanned! {span=>
            #[prusti::pure]
        }],
    ))
}

/// Generate spec items and attributes to typecheck and later retrieve "verified" annotations.
fn generate_for_verified(
    attr: TokenStream,
    span: Span,
    _item: &untyped::AnyFnItem,
) -> GeneratedResult {
    if !attr.is_empty() {
        return Err(syn::Error::new(
            attr.span(),
            "the `#[verified]` attribute does not take parameters",
        ));
    }

    Ok((
        vec![],
        vec![parse_quote_spanned! {span=>
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
fn generate_for_trusted(
    attr: TokenStream,
    span: Span,
    _item: &untyped::AnyFnItem,
) -> GeneratedResult {
    if !attr.is_empty() {
        return Err(syn::Error::new(
            attr.span(),
            "the `#[trusted]` attribute does not take parameters",
        ));
    }

    Ok((
        vec![],
        vec![parse_quote_spanned! {span=>
            #[prusti::trusted]
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

/// Rejects `result` as a binding anywhere in a closure parameter pattern: it
/// would collide with the postcondition closure's `result` parameter.
fn check_no_result_binding(pat: &syn::Pat) -> syn::Result<()> {
    struct FindResult(Option<Span>);
    impl<'ast> syn::visit::Visit<'ast> for FindResult {
        fn visit_pat_ident(&mut self, pat: &'ast syn::PatIdent) {
            if self.0.is_none() && pat.ident == "result" {
                self.0 = Some(pat.ident.span());
            }
            syn::visit::visit_pat_ident(self, pat);
        }
    }
    let mut visitor = FindResult(None);
    syn::visit::Visit::visit_pat(&mut visitor, pat);
    match visitor.0 {
        Some(span) => Err(syn::Error::new(
            span,
            "closure parameter bindings may not be named `result`",
        )),
        None => Ok(()),
    }
}

/// The value of a closure parameter, rebuilt from its pattern's bindings for
/// the `closure_spec_*` marker tuples. The value sits in dead code and only
/// pins the spec closures' parameter types, but it must typecheck: a pattern
/// without `..` and without `ref` bindings binds everything it matches, so
/// its value can be rebuilt structurally (moving the bindings, which the
/// diverging `return` permits).
///
/// `_` binds nothing, and nothing can mention it either, but the stand-in
/// value must still typecheck at its position. In a structural position
/// (a tuple slot, behind `&`, or the parameter itself) the expected type is
/// whatever we build, so `()` serves. In a `pinned` position (the field of
/// a struct the pattern names, or an array's element type, unified with the
/// sibling elements) no stand-in can be right: the field's type is fixed
/// by a definition this macro cannot see, so `()` mismatches a concrete
/// field, while an inference variable (`None.unwrap()`) is unresolvable
/// when `_` is all that constrains a generic one. Such a `_` is therefore
/// rejected; binding the value instead (`_x`) is exact in both cases.
fn reconstruct_arg(pat: &syn::Pat, pinned: bool) -> syn::Result<TokenStream> {
    let unsupported = |span, what: &str| {
        syn::Error::new(
            span,
            format!("the parameters of a closure with specifications may not contain {what}"),
        )
    };
    match pat {
        syn::Pat::Ident(pat_ident) => {
            if let Some(by_ref) = &pat_ident.by_ref {
                return Err(unsupported(by_ref.span(), "`ref` bindings"));
            }
            // An `x @ subpattern` binding names the whole value, whatever
            // the subpattern is.
            let ident = &pat_ident.ident;
            Ok(quote_spanned! {ident.span()=> #ident })
        }
        syn::Pat::Wild(wild) if pinned => Err(unsupported(
            wild.span(),
            "`_` inside a struct or array pattern (bind the value instead, e.g. `_x`)",
        )),
        syn::Pat::Wild(wild) => Ok(quote_spanned! {wild.span()=> () }),
        // A tuple (or reference) type is structural: if the position of the
        // whole is pinned, so is each slot, and vice versa.
        syn::Pat::Tuple(tuple) => {
            let elems = tuple
                .elems
                .iter()
                .map(|elem| reconstruct_arg(elem, pinned))
                .collect::<syn::Result<Vec<_>>>()?;
            Ok(quote_spanned! {tuple.span()=> (#(#elems,)*) })
        }
        syn::Pat::Reference(reference) => {
            let mutability = &reference.mutability;
            let value = reconstruct_arg(&reference.pat, pinned)?;
            Ok(quote_spanned! {reference.span()=> &#mutability #value })
        }
        // A constructor is a nominal signature: its fields' types are fixed
        // by the struct definition, whatever the position of the whole.
        syn::Pat::TupleStruct(tuple_struct) => {
            let path = &tuple_struct.path;
            let elems = tuple_struct
                .pat
                .elems
                .iter()
                .map(|elem| reconstruct_arg(elem, true))
                .collect::<syn::Result<Vec<_>>>()?;
            Ok(quote_spanned! {tuple_struct.span()=> #path(#(#elems),*) })
        }
        syn::Pat::Struct(pat_struct) => {
            if let Some(dot2) = &pat_struct.dot2_token {
                return Err(unsupported(dot2.span(), "`..`"));
            }
            let path = &pat_struct.path;
            let fields = pat_struct
                .fields
                .iter()
                .map(|field| {
                    let member = &field.member;
                    let value = reconstruct_arg(&field.pat, true)?;
                    Ok(quote_spanned! {field.span()=> #member: #value })
                })
                .collect::<syn::Result<Vec<_>>>()?;
            Ok(quote_spanned! {pat_struct.span()=> #path { #(#fields),* } })
        }
        // A slice pattern in parameter position matches an array (on a slice
        // it would be refutable, which rustc rejects on its own), so the
        // value is an array literal. The elements share one type, so each
        // slot is pinned by its siblings.
        syn::Pat::Slice(slice) => {
            let elems = slice
                .elems
                .iter()
                .map(|elem| reconstruct_arg(elem, true))
                .collect::<syn::Result<Vec<_>>>()?;
            Ok(quote_spanned! {slice.span()=> [#(#elems),*] })
        }
        // A unit struct: the path is the value.
        syn::Pat::Path(path) => Ok(path.to_token_stream()),
        syn::Pat::Type(pat_type) => reconstruct_arg(&pat_type.pat, pinned),
        syn::Pat::Rest(rest) => Err(unsupported(rest.span(), "`..`")),
        other => Err(unsupported(other.span(), "this kind of pattern")),
    }
}

/// Expands the `closure!` macro: returns the closure itself, with its specs
/// embedded as `closure_spec_*` marker calls in dead `if false { return .. }`
/// blocks inside the body (the `return` makes the argument moves diverge, so
/// they cannot affect the body), one block per specification. For
///
/// ```ignore
/// closure!(#[requires(P1)] #[requires(P2)] #[ensures(Q)] |a: A, b| body)
/// ```
///
/// the macro expands to
///
/// ```ignore
/// {
///     #[prusti::closure]
///     #[prusti::specs_version = "..."]
///     let _prusti_closure = |a: A, b| {
///         if false {
///             return closure_spec_pre((a, b), #[prusti::spec_only] |a: _, b: _| -> bool { P1 });
///         }
///         if false {
///             return closure_spec_pre((a, b), #[prusti::spec_only] |a: _, b: _| -> bool { P2 });
///         }
///         let prusti_closure_args = ::core::marker::PhantomData;    // mixed-site hygiene
///         if false {
///             return closure_spec_args((a, b, None.unwrap()), prusti_closure_args);
///         }
///         let result = body;
///         if false {
///             return closure_spec_post((None.unwrap(), None.unwrap(), result), prusti_closure_args, #[prusti::spec_only] |a: _, b: _, result| -> bool { Q });
///         }
///         result
///     };
///     _prusti_closure
/// }
/// ```
///
/// Each spec closure carries the span of its specification, so that
/// diagnostics point at the violated clause.
///
/// The spec closures take the closure's parameters (plus `result` for
/// postconditions) as a flat list of the parameters' own patterns; their
/// types are deduced from the markers' `Fn<Args>` bound against the actual
/// argument tuple, never from annotations (see [reconstruct_arg]: a `_`
/// slot's stand-in value deliberately fakes its type, so a user annotation
/// must not be forwarded). The argument tuple holds each parameter's value,
/// rebuilt from the pattern's bindings for parameters that destructure.
/// `closure_spec_args` unifies the `PhantomData` binding
/// carrying the argument (and result) types from the closure entry to the
/// postcondition; tuple slots whose values are unavailable at the
/// respective marker are filled with `None.unwrap()`, which mints a fresh
/// inference variable (a `!`-typed stand-in such as `unreachable!()` wouldn't
/// work as it doesn't coerce at that point and would pin the slot to `!`).
pub fn closure(tokens: TokenStream) -> TokenStream {
    let cl_spec: ClosureWithSpec = handle_result!(syn::parse(tokens.into()));
    let callsite_span = Span::call_site();

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

    let mut attrs_ts = TokenStream::new();
    for a in attrs {
        match a.path.get_ident() {
            Some(ident) if ident == "pure" => {
                attrs_ts.extend(quote_spanned! {a.span()=> #[prusti::pure] });
            }
            Some(ident) if ident == "trusted" => {
                attrs_ts.extend(quote_spanned! {a.span()=> #[prusti::trusted] });
            }
            // Reject other specification attributes rather than forwarding
            // them (they would be silently ignored on the `let` binding).
            Some(ident) if SpecAttributeKind::try_from(ident.to_string()).is_ok() => {
                return syn::Error::new(
                    a.span(),
                    format!("`{ident}` is not supported on `closure!`"),
                )
                .to_compile_error();
            }
            _ => attrs_ts.extend(a.into_token_stream()),
        }
    }

    // Each specification with its span, so that the spec closure carries the
    // span of its expression and diagnostics point at that clause.
    let parse_specs = |exprs: Vec<syn::Expr>| -> syn::Result<Vec<(TokenStream, Span)>> {
        exprs
            .into_iter()
            .map(|expr| Ok((parse_prusti(expr.to_token_stream())?, expr.span())))
            .collect()
    };
    let pres = handle_result!(parse_specs(cl_spec.pres));
    let posts = handle_result!(parse_specs(cl_spec.posts));

    // The spec closures' parameters (the closure's own patterns) and the
    // parameters' values for the marker tuples (rebuilt from the patterns'
    // bindings). The parameter types are deliberately left to inference:
    // each is pinned by its value, and for a pattern with `_` slots the
    // value's type differs from the closure's (the slots hold `()`), so a
    // user annotation must not be forwarded.
    let mut spec_params: Vec<TokenStream> = vec![];
    let mut arg_values: Vec<TokenStream> = vec![];
    if !pres.is_empty() || !posts.is_empty() {
        for input in &inputs {
            let pat = match input {
                syn::Pat::Type(pat_type) => &*pat_type.pat,
                other => other,
            };
            handle_result!(check_no_result_binding(pat));
            arg_values.push(handle_result!(reconstruct_arg(pat, false)));
            spec_params.push(quote_spanned! {callsite_span=> #pat: _ });
        }
    }

    let anys = arg_values
        .iter()
        .map(|_| quote_spanned! {callsite_span=> ::core::option::Option::None.unwrap() })
        .collect::<Vec<_>>();
    let result_param = match &output {
        syn::ReturnType::Type(_, ty) => quote_spanned! {callsite_span=> result: #ty },
        syn::ReturnType::Default => quote_spanned! {callsite_span=> result },
    };

    // Hygienic: user code inside the closure body cannot refer to this binding.
    let args_ident = syn::Ident::new("prusti_closure_args", Span::mixed_site());

    let pre_stmts = pres.iter().map(|(pre, span)| {
        let spec_closure = quote_spanned! {*span=>
            #[prusti::spec_only]
            |#(#spec_params),*| -> bool { #pre }
        };
        quote_spanned! {callsite_span=>
            #[allow(unused_must_use, unused_variables, unused_braces, unused_parens)]
            if false {
                return ::prusti_contracts::closure_spec_pre((#(#arg_values,)*), #spec_closure);
            }
        }
    });

    // The `PhantomData` tie is only needed (and only typechecks, its result
    // slot being pinned by the post markers alone) when there are
    // postconditions.
    let body = if posts.is_empty() {
        body.to_token_stream()
    } else {
        let post_stmts = posts.iter().map(|(post, span)| {
            let spec_closure = quote_spanned! {*span=>
                #[prusti::spec_only]
                |#(#spec_params,)* #result_param| -> bool { #post }
            };
            quote_spanned! {callsite_span=>
                #[allow(unused_must_use, unused_variables, unused_braces, unused_parens)]
                if false {
                    return ::prusti_contracts::closure_spec_post(
                        (#(#anys,)* result,),
                        #args_ident,
                        #spec_closure,
                    );
                }
            }
        });
        quote_spanned! {callsite_span=>
            let #args_ident = ::core::marker::PhantomData;
            #[allow(unused_must_use, unused_braces, unused_parens)]
            if false {
                return ::prusti_contracts::closure_spec_args(
                    (#(#arg_values,)* ::core::option::Option::None.unwrap(),),
                    #args_ident,
                );
            }
            let result = #body;
            #(#post_stmts)*
            result
        }
    };
    let new_body = quote_spanned! {callsite_span=>
        {
            #(#pre_stmts)*
            #body
        }
    };

    quote_spanned! {callsite_span=>
        {
            #[allow(unused_variables, unused_braces, unused_parens)]
            #[prusti::closure]
            #[prusti::specs_version = #SPECS_VERSION]
            #attrs_ts
            let _prusti_closure =
                #asyncness #movability #capture
                #or1_token #inputs #or2_token #output
                #new_body;
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
                    .filter(|(kind, _, _)| kind == &SpecAttributeKind::RefineSpec)
                    .map(|(_, _, tokens)| tokens.span())
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

                let ParsedPredicate::Impl(predicate) = parsed_predicate else {
                    unreachable!()
                };

                // Patch spec function: Rewrite self with _self: <SpecStruct>
                let syn::Item::Fn(spec_function) = predicate.spec_function else {
                    unreachable!()
                };
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
        #[prusti::refine_trait_spec]
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

pub fn invariant(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id = rewriter.generate_spec_id();
    let spec_id_str = spec_id.to_string();

    let item: syn::DeriveInput = handle_result!(syn::parse2(tokens));
    let item_span = item.span();
    let item_ident = item.ident.clone();
    let item_name = syn::Ident::new(
        &format!("prusti_invariant_item_{item_ident}_{spec_id}"),
        item_span,
    );

    let attr = handle_result!(parse_prusti(attr));

    // TODO: move some of this to AstRewriter?
    // see AstRewriter::generate_spec_item_fn for explanation of syntax below
    let spec_item: syn::ItemFn = parse_quote_spanned! {item_span=>
        #[allow(unused_must_use, unused_parens, unused_variables, dead_code, non_snake_case)]
        #[prusti::spec_only]
        #[prusti::type_invariant_spec]
        #[prusti::spec_id = #spec_id_str]
        fn #item_name(self) -> bool {
            let val: bool = #attr;
            val
        }
    };

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
                    SpecAttributeKind::Trusted | SpecAttributeKind::Model => {
                        assert!(attr.tokens.is_empty(), "Unexpected shape of an attribute.");
                        attr.tokens
                    }
                    SpecAttributeKind::PrintCounterexample => {
                        // We need to drop the surrounding parenthesis to make the
                        // tokens identical to the ones passed by the native procedural
                        // macro call.
                        let mut iter = attr.tokens.into_iter();
                        let TokenTree::Group(group) = iter.next().unwrap() else {
                            unreachable!()
                        };
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
pub fn ghost(tokens: TokenStream) -> TokenStream {
    let mut rewriter = rewriter::AstRewriter::new();
    let callsite_span = Span::call_site();

    let spec_id = rewriter.generate_spec_id();
    let spec_id_str = spec_id.to_string();

    struct Visitor {
        loops: Vec<(Option<syn::Ident>, Span)>,
        breaks: Vec<(Option<syn::Ident>, Span)>,
        returns: Option<Span>,
        tries: Vec<Span>,
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
        // `?` exits the enclosing function like `return` does.
        fn visit_expr_try(&mut self, ex: &'ast syn::ExprTry) {
            self.tries.push(ex.span());
            syn::visit::visit_expr_try(self, ex);
        }
        // Do not descend into nested closures or items: `return`/`?` (and
        // loops) inside them are local to the closure/item and do not leave
        // the ghost block.
        fn visit_expr_closure(&mut self, _: &'ast syn::ExprClosure) {}
        fn visit_item(&mut self, _: &'ast syn::Item) {}
    }

    let mut visitor = Visitor {
        loops: vec![],
        breaks: vec![],
        returns: None,
        tries: vec![],
    };

    let tokens = quote! {
        {#tokens}
    };

    let input = syn::parse::<syn::Block>(tokens.clone().into()).unwrap();

    visitor.visit_block(&input);

    let mut exit_errors = visitor.returns.into_iter().collect::<Vec<_>>();
    exit_errors.extend(visitor.tries);

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

    // The ghost body lives in dead code, so it is pruned before codegen; the
    // live path merely constructs the `Ghost` ZST. The body appears twice:
    // inline (encoded for verification) and duplicated into a never-called
    // closure so that the compiler checks it complies with `Fn` capture rules
    // (no mutation or consumption of outer variables); `ghost_call`'s
    // signature unifies the types of the two copies. The `if`/`else` unifies
    // the types of the two arms, giving `ghost_erased()` the body's type.
    if exit_errors.is_empty() {
        quote_spanned! {callsite_span=>
            #[allow(unused_must_use, unused_variables, unused_braces, unused_parens)]
            if false {
                ::prusti_contracts::ghost_call(
                    &(
                        #[prusti::spec_only]
                        #[prusti::spec_id = #spec_id_str]
                        #[prusti::specs_version = #SPECS_VERSION]
                        || {#tokens}
                    ),
                    {#tokens},
                )
            } else {
                ::prusti_contracts::ghost_erased()
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
