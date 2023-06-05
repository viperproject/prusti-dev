//! Predicate parsing

use crate::{
    common::{HasMacro, HasSignature},
    rewriter, SpecificationId, SPECS_VERSION,
};
use proc_macro2::{Span, TokenStream};
use quote::{quote_spanned, ToTokens};
use syn::{parse::Parse, parse_quote_spanned, spanned::Spanned, FnArg, Type};

/*
#[derive(Debug)]
pub struct PredicateWithBody<T: ToTokens> {
    /// The function which was inside the macro to be used at the definition-site of the macro
    /// The body of the function is replaced (`unimplemented!()`)
    pub patched_function: T,
    pub spec_function: syn::Item,
}

impl<T: ToTokens> ToTokens for PredicateWithBody<T> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.spec_function.to_tokens(tokens);
        self.patched_function.to_tokens(tokens);
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
*/

#[derive(Debug)]
pub struct ParsedObligation {
    patched: syn::ItemFn
}

impl ToTokens for ParsedObligation {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.patched.to_tokens(tokens);
    }
}

fn has_valid_amount_arg(obligation_sig: &syn::Signature) -> bool {
    obligation_sig.inputs.first().map_or(false, |arg| {
        let token_strings = arg
            .into_token_stream()
            .into_iter()
            .map(|tok| tok.to_string())
            .collect::<Vec<_>>();
        token_strings == vec!["amount", ":", "usize"]
    })
}

pub fn parse_obligation(//_internal(
    tokens: TokenStream,
    //in_spec_refinement: bool,
) -> syn::Result<ParsedObligation> {
    let span = tokens.span();
    let input: ObligationFnInput = syn::parse2(tokens).map_err(|e| {
        syn::Error::new(
            e.span(),
            "`obligation!` can only be used on function definitions; it supports no attributes",
        )
    })?;
    match &input.fn_sig.output {
        syn::ReturnType::Type(..) => {
            return Err(syn::Error::new(
                input.fn_sig.span(),
                "`obligation!` shall not specify an output type",
            ));
        }
        syn::ReturnType::Default => {}
        /*
=> typ.to_token_stream(),
        syn::ReturnType::Default => {
            return Err(syn::Error::new(
                input.fn_sig.span(),
                "`predicate!` must specify an output type",
            ));
        }
        */
    };

    if input.body.is_some() {
            return Err(syn::Error::new(
                input.body.span(),
                "`obligation!` shall not provide a body",
            ));
            /*
        let mut rewriter = rewriter::AstRewriter::new();
        let spec_id = rewriter.generate_spec_id();

        if in_spec_refinement {
            let patched_function: syn::ImplItemMethod =
                patch_predicate_macro_body(&input, span, spec_id);
            let spec_function = generate_spec_function(
                input.body.unwrap(),
                return_type,
                spec_id,
                &patched_function,
            )?;

            Ok(ParsedPredicate::Impl(PredicateWithBody {
                spec_function,
                patched_function,
            }))
        } else {
            let patched_function: syn::ItemFn = patch_predicate_macro_body(&input, span, spec_id);
            let spec_function = generate_spec_function(
                input.body.unwrap(),
                return_type,
                spec_id,
                &patched_function,
            )?;

            Ok(ParsedPredicate::FreeStanding(PredicateWithBody {
                spec_function,
                patched_function,
            }))
        }
        */
    } else if !has_valid_amount_arg(&input.fn_sig) {
        return Err(syn::Error::new(
                input.body.span(),
                "the first argument of an obligation in `obligation!` must be `amount: usize`",
        ));
    } else {
        let signature = input.fn_sig;
        let patched = parse_quote_spanned!(span=>
            #[prusti::obligation]
            #[prusti::specs_version = #SPECS_VERSION]
            #signature -> bool { unimplemented!(); }
        );

        Ok(ParsedObligation {
            patched,
        })
    }
}

/*
fn patch_predicate_macro_body<R: Parse>(
    predicate: &PredicateFnInput,
    input_span: Span,
    spec_id: SpecificationId,
) -> R {
    let visibility = &predicate.visibility;
    let signature = &predicate.fn_sig;
    let spec_id_str = spec_id.to_string();

    parse_quote_spanned!(input_span=>
        #[allow(unused_must_use, unused_variables, dead_code)]
        #[prusti::pred_spec_id_ref = #spec_id_str]
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
*/

#[derive(Debug)]
struct ObligationFnInput {
    visibility: Option<syn::Visibility>,
    fn_sig: syn::Signature,
    body: Option<TokenStream>,
}

impl syn::parse::Parse for ObligationFnInput {
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

        Ok(ObligationFnInput {
            visibility,
            fn_sig,
            body,
        })
    }
}
