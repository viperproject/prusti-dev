//! Obligation parsing

use crate::SPECS_VERSION;
use proc_macro2::TokenStream;
use quote::{quote_spanned, ToTokens};
use syn::{parse_quote_spanned, spanned::Spanned};

// TODO: reduce code duplication with predicate parsing (?)

#[derive(Debug)]
pub struct ParsedObligation {
    patched: syn::ItemFn,
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

pub fn parse_obligation(tokens: TokenStream) -> syn::Result<ParsedObligation> {
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
    };

    if input.body.is_some() {
        return Err(syn::Error::new(
            input.body.span(),
            "`obligation!` shall not provide a body",
        ));
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

        Ok(ParsedObligation { patched })
    }
}

#[derive(Debug)]
struct ObligationFnInput {
    fn_sig: syn::Signature,
    body: Option<TokenStream>,
}

impl syn::parse::Parse for ObligationFnInput {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
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

        Ok(ObligationFnInput { fn_sig, body })
    }
}
