//! Resource and obligation parsing

use crate::SPECS_VERSION;
use proc_macro2::TokenStream;
use quote::{quote_spanned, ToTokens};
use syn::{parse_quote, parse_quote_spanned, spanned::Spanned};

// TODO: reduce code duplication with predicate parsing (?)

#[derive(Debug)]
pub struct ParsedResource {
    patched: syn::ItemFn,
}

impl ToTokens for ParsedResource {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.patched.to_tokens(tokens);
    }
}

fn has_valid_amount_arg(resource_sig: &syn::Signature) -> bool {
    resource_sig.inputs.first().map_or(false, |arg| {
        let token_strings = arg
            .into_token_stream()
            .into_iter()
            .map(|tok| tok.to_string())
            .collect::<Vec<_>>();
        token_strings == vec!["amount", ":", "usize"]
    })
}

pub fn parse_resource(tokens: TokenStream) -> syn::Result<ParsedResource> {
    parse_resource_internal(tokens, "resource", parse_quote!(#[prusti::resource]))
}

pub fn parse_obligation(tokens: TokenStream) -> syn::Result<ParsedResource> {
    parse_resource_internal(tokens, "obligation", parse_quote!(#[prusti::obligation]))
}

fn parse_resource_internal(
    tokens: TokenStream,
    macro_name: &str,
    output_attribute: TokenStream,
) -> syn::Result<ParsedResource> {
    let span = tokens.span();
    let parse_res = syn::parse2(tokens);
    let input: ResourceFnInput = parse_res.map_err(|e| {
        syn::Error::new(
            e.span(),
            format!("`{}!` can only be used on function definitions", macro_name),
        )
    })?;

    for attribute in &input.attributes {
        if attribute
            .path
            .to_token_stream()
            .into_iter()
            .map(|tok| tok.to_string())
            .collect::<Vec<_>>()
            != vec!["doc"]
        {
            return Err(syn::Error::new(
                attribute.span(),
                format!(
                    "the function in `{}!` shall have only doc attributes",
                    macro_name
                ),
            ));
        }
    }

    match &input.fn_sig.output {
        syn::ReturnType::Type(..) => {
            return Err(syn::Error::new(
                input.fn_sig.span(),
                format!(
                    "the function in `{}!` shall not specify an output type",
                    macro_name
                ),
            ));
        }
        syn::ReturnType::Default => {}
    };

    if input.body.is_some() {
        Err(syn::Error::new(
            input.body.span(),
            format!("the function in `{}!` shall not provide a body", macro_name),
        ))
    } else if !has_valid_amount_arg(&input.fn_sig) {
        let error_span = if let Some(arg) = input.fn_sig.inputs.first() {
            arg.span()
        } else {
            input.fn_sig.span()
        };
        Err(syn::Error::new(
            error_span,
            format!(
                "the first argument of the function in `{}!` must be `amount: usize`",
                macro_name
            ),
        ))
    } else {
        let attribute_tokens =
            input
                .attributes
                .into_iter()
                .fold(TokenStream::new(), |mut tokens, attribute| {
                    attribute.to_tokens(&mut tokens);
                    tokens
                });
        let visibility = input.visibility;
        let signature = input.fn_sig;
        let patched = parse_quote_spanned!(span=>
            #attribute_tokens
            #output_attribute
            #[prusti::specs_version = #SPECS_VERSION]
            #[allow(unused_variables)]
            #visibility #signature -> bool { unimplemented!(); }
        );

        Ok(ParsedResource { patched })
    }
}

#[derive(Debug)]
struct ResourceFnInput {
    attributes: Vec<syn::Attribute>,
    visibility: syn::Visibility,
    fn_sig: syn::Signature,
    body: Option<TokenStream>,
}

impl syn::parse::Parse for ResourceFnInput {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let attributes = input.call(syn::Attribute::parse_outer)?;
        let visibility = input.parse()?;
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

        Ok(ResourceFnInput {
            attributes,
            visibility,
            fn_sig,
            body,
        })
    }
}
