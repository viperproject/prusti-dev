use crate::ast::*;
use syn::{
    bracketed, parenthesized,
    parse::{Parse, ParseStream},
    parse_quote, Token,
};

mod kw {
    syn::custom_keyword!(derive);
    syn::custom_keyword!(new);
    syn::custom_keyword!(new_with_pos);
    syn::custom_keyword!(Hash);
    syn::custom_keyword!(PartialEq);
    syn::custom_keyword!(Ord);
    syn::custom_keyword!(ignore);
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

impl Parse for CopyModule {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let path = input.parse()?;
        Ok(Self { path })
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

impl Parse for DeriveLower {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let is_self_mut = if input.peek(syn::Token![mut]) {
            input.parse::<syn::Token![mut]>()?;
            true
        } else {
            false
        };
        let user_trait_ident = input.parse()?;
        input.parse::<Token![,]>()?;
        let deriver_trait_ident = input.parse()?;
        input.parse::<Token![:]>()?;
        let source_type = input.parse()?;
        input.parse::<Token![=>]>()?;
        let target_type = input.parse()?;
        Ok(Self {
            is_self_mut,
            user_trait_ident,
            deriver_trait_ident,
            source_type,
            target_type,
        })
    }
}

impl Parse for CustomDeriveOptions {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        input.parse::<kw::ignore>()?;
        input.parse::<Token![=]>()?;
        let content;
        bracketed!(content in input);
        let fields =
            syn::punctuated::Punctuated::<_, Token![,]>::parse_separated_nonempty(&content)?;
        Ok(Self {
            ignored_fields: fields.into_iter().collect(),
        })
    }
}

impl Parse for CustomDerive {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let lookahead = input.lookahead1();
        let derive = if lookahead.peek(kw::new) {
            input.parse::<kw::new>()?;
            Self::New
        } else if lookahead.peek(kw::new_with_pos) {
            input.parse::<kw::new_with_pos>()?;
            Self::NewWithPos
        } else if lookahead.peek(kw::PartialEq) && input.peek2(syn::token::Paren) {
            input.parse::<kw::PartialEq>()?;
            let content;
            parenthesized!(content in input);
            Self::PartialEq(CustomDeriveOptions::parse(&content)?)
        } else if lookahead.peek(kw::Ord) && input.peek2(syn::token::Paren) {
            input.parse::<kw::Ord>()?;
            let content;
            parenthesized!(content in input);
            Self::Ord(CustomDeriveOptions::parse(&content)?)
        } else if lookahead.peek(kw::Hash) && input.peek2(syn::token::Paren) {
            input.parse::<kw::Hash>()?;
            let content;
            parenthesized!(content in input);
            Self::Hash(CustomDeriveOptions::parse(&content)?)
        } else {
            Self::Other(input.parse()?)
        };
        Ok(derive)
    }
}

impl Parse for CustomDeriveList {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let content;
        parenthesized!(content in input);
        let list = Self {
            derives: syn::punctuated::Punctuated::parse_terminated(&content)?,
        };
        Ok(list)
    }
}
