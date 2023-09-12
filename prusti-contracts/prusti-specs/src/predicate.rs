//! Predicate parsing

use crate::{
    common::{HasMacro, HasSignature},
    expression_with_attributes::AttributeConsumer,
    rewriter,
    runtime_checks::translation::translate_predicate,
    specifications::preparser::parse_prusti,
    SpecificationId, SPECS_VERSION,
};
use proc_macro2::{Span, TokenStream};
use quote::{quote_spanned, ToTokens};
use syn::{parse::Parse, parse_quote_spanned, spanned::Spanned};

#[derive(Debug)]
pub struct PredicateWithBody<T: ToTokens> {
    /// The function which was inside the macro to be used at the definition-site of the macro
    /// The body of the function is replaced (`unimplemented!()`)
    pub patched_function: T,
    pub spec_function: syn::Item,
    pub check_function: Option<syn::Item>,
}

impl<T: ToTokens> ToTokens for PredicateWithBody<T> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.spec_function.to_tokens(tokens);
        self.patched_function.to_tokens(tokens);
        self.check_function.to_tokens(tokens);
    }
}

#[derive(Debug)]
pub struct PredicateWithoutBody {
    /// The function which was inside the macro to be used at the definition-site of the macro
    patched_function: syn::TraitItemMethod,
}

impl ToTokens for PredicateWithoutBody {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let patched_function = &self.patched_function;
        patched_function.to_tokens(tokens);
    }
}

#[derive(Debug)]
pub enum ParsedPredicate {
    /// An abstract predicate, which can appear in trait methods
    Abstract(PredicateWithoutBody),

    /// A predicate which implements an abstract predicate
    Impl(PredicateWithBody<syn::ImplItemMethod>),

    /// A free-standing predicate (for free-standing functions)
    FreeStanding(PredicateWithBody<syn::ItemFn>),
}

impl ToTokens for ParsedPredicate {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Self::FreeStanding(p) => p.to_tokens(tokens),
            Self::Abstract(p) => p.to_tokens(tokens),
            Self::Impl(p) => p.to_tokens(tokens),
        }
    }
}

pub(crate) fn is_predicate_macro<T: HasMacro>(makro: &T) -> bool {
    makro
        .mac()
        .path
        .segments
        .last()
        .map(|last| last.ident == "predicate")
        .unwrap_or(false)
}

pub fn parse_predicate_in_impl(tokens: TokenStream) -> syn::Result<ParsedPredicate> {
    parse_predicate_internal(tokens, true)
}

pub fn parse_predicate(tokens: TokenStream) -> syn::Result<ParsedPredicate> {
    parse_predicate_internal(tokens, false)
}

fn parse_predicate_internal(
    tokens: TokenStream,
    in_spec_refinement: bool,
) -> syn::Result<ParsedPredicate> {
    let span = tokens.span();
    let mut attr_consumer: AttributeConsumer = syn::parse(tokens.into())?;
    let runtime_checkable = attr_consumer
        .get_attribute("insert_runtime_check")
        .is_some();
    // attr_consumer.check_no_remaining_attrs()?;
    let tokens = attr_consumer.tokens();
    let input: PredicateFnInput = syn::parse2(tokens).map_err(|e| {
        syn::Error::new(
            e.span(),
            "`predicate!` can only be used on function definitions; it supports no attributes",
        )
    })?;
    let return_type = match &input.fn_sig.output {
        syn::ReturnType::Default => {
            return Err(syn::Error::new(
                input.fn_sig.span(),
                "`predicate!` must specify an output type",
            ));
        }
        syn::ReturnType::Type(_, box typ) => typ.to_token_stream(),
    };

    if input.body.is_some() {
        let mut rewriter = rewriter::AstRewriter::new();
        let spec_id = rewriter.generate_spec_id();
        let check_id_opt = runtime_checkable.then_some(rewriter.generate_spec_id());

        if in_spec_refinement {
            let patched_function: syn::ImplItemMethod =
                patch_predicate_macro_body(&input, span, spec_id, check_id_opt);
            let body = input.body.unwrap();
            let spec_function =
                generate_spec_function(body.clone(), return_type, spec_id, &patched_function)?;
            let check_function = if runtime_checkable {
                Some(translate_predicate(
                    check_id_opt.unwrap(),
                    parse_prusti(body)?,
                    &patched_function,
                )?)
            } else {
                None
            };

            Ok(ParsedPredicate::Impl(PredicateWithBody {
                spec_function,
                patched_function,
                check_function,
            }))
        } else {
            let patched_function: syn::ItemFn =
                patch_predicate_macro_body(&input, span, spec_id, check_id_opt);
            let body = input.body.unwrap();
            let spec_function =
                generate_spec_function(body.clone(), return_type, spec_id, &patched_function)?;
            let check_function = if runtime_checkable {
                Some(translate_predicate(
                    check_id_opt.unwrap(),
                    parse_prusti(body)?,
                    &patched_function,
                )?)
            } else {
                None
            };

            Ok(ParsedPredicate::FreeStanding(PredicateWithBody {
                spec_function,
                patched_function,
                check_function,
            }))
        }
    } else {
        if runtime_checkable {
            return Err(syn::Error::new(
                span,
                "Abstract predicates can not be runtime checked",
            ));
        }
        let signature = input.fn_sig;
        let patched_function = parse_quote_spanned!(span=>
            #[prusti::abstract_predicate]
            #[prusti::specs_version = #SPECS_VERSION]
            #signature;
        );

        Ok(ParsedPredicate::Abstract(PredicateWithoutBody {
            patched_function,
        }))
    }
}

fn patch_predicate_macro_body<R: Parse>(
    predicate: &PredicateFnInput,
    input_span: Span,
    spec_id: SpecificationId,
    check_id_opt: Option<SpecificationId>,
) -> R {
    let visibility = &predicate.visibility;
    let signature = &predicate.fn_sig;
    let spec_id_str = spec_id.to_string();
    let check_ref_attr = check_id_opt.map(|id| {
        let check_id_str = id.to_string();
        quote_spanned!(input_span => #[prusti::pred_check_id_ref = #check_id_str])
    });

    parse_quote_spanned!(input_span=>
        #[allow(unused_must_use, unused_variables, dead_code)]
        #[prusti::pred_spec_id_ref = #spec_id_str]
        #check_ref_attr
        #[prusti::specs_version = #SPECS_VERSION]
        #visibility #signature {
            unimplemented!("predicate")
        }
    )
}

fn generate_spec_function<T: HasSignature + Spanned>(
    body: TokenStream,
    return_type: TokenStream,
    spec_id: SpecificationId,
    patched_function: &T,
) -> syn::Result<syn::Item> {
    let mut rewriter = rewriter::AstRewriter::new();
    rewriter.process_assertion(
        rewriter::SpecItemType::Predicate(return_type),
        spec_id,
        body,
        patched_function,
    )
}

#[derive(Debug)]
struct PredicateFnInput {
    visibility: Option<syn::Visibility>,
    fn_sig: syn::Signature,
    body: Option<TokenStream>,
}

impl syn::parse::Parse for PredicateFnInput {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let visibility = input.parse().ok();
        let fn_sig = input.parse()?;

        let body = if input.peek(syn::Token![;]) {
            let _semi: syn::Token![;] = input.parse()?;
            None
        } else {
            let brace_content;
            let _brace_token = syn::braced!(brace_content in input);
            let parsed_body: TokenStream = brace_content.parse()?;
            // add the braces back to allow function-like syntax
            Some(quote_spanned!(parsed_body.span()=> { #parsed_body }))
        };

        Ok(PredicateFnInput {
            visibility,
            fn_sig,
            body,
        })
    }
}
