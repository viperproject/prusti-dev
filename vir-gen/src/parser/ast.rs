use syn::{
    parse::{Parse, ParseStream},
    parse_quote, Token,
};

use crate::ast::*;

mod kw {
    syn::custom_keyword!(derive);
}

impl Parse for Declarations {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let components_ident: syn::Ident = input.parse()?;
        let components = parse_quote! {
            mod #components_ident;
        };
        input.parse::<Token![=>]>()?;
        let mut irs = Vec::new();
        while !input.is_empty() {
            irs.push(input.parse()?);
        }
        Ok(Self { components, irs })
    }
}

impl Parse for TypeImport {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let name: syn::Ident = input.parse()?;
        let alias = if input.peek(Token![as]) {
            input.parse::<Token![as]>()?;
            input.parse()?
        } else {
            name.clone()
        };
        Ok(Self { name, alias })
    }
}

impl Parse for Include {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let path = input.parse()?;
        input.parse::<Token![=>]>()?;
        let mut imported_types = Vec::new();
        let mut derive_macros = Vec::new();
        while !input.is_empty() {
            let lookahead = input.lookahead1();
            if lookahead.peek(Token![use]) {
                input.parse::<Token![use]>()?;
                imported_types.push(input.parse()?);
                input.parse::<Token![;]>()?;
            } else if lookahead.peek(kw::derive) {
                input.parse::<kw::derive>()?;
                derive_macros.push(input.parse()?);
                while input.peek(Token![,]) {
                    input.parse::<Token![,]>()?;
                    derive_macros.push(input.parse()?);
                }
                input.parse::<Token![;]>()?;
            } else {
                return Err(lookahead.error());
            }
        }
        Ok(Self {
            path,
            imported_types,
            derive_macros,
        })
    }
}

impl Parse for IdentList {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Self {
            idents: syn::punctuated::Punctuated::parse_separated_nonempty(input)?,
        })
    }
}

impl Parse for RawBlock {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let name = input.parse()?;
        input.parse::<Token![=>]>()?;
        let mut content = Vec::new();
        while !input.is_empty() {
            content.push(input.parse()?);
        }
        Ok(Self { name, content })
    }
}
