use proc_macro2::{TokenStream, TokenTree};
use rustc_hash::FxHashMap;

#[derive(Debug, Default)]
pub(crate) struct SpecProperties {
    properties: FxHashMap<String, String>
}

pub(crate) enum Property {
    Translator,
    File
}

impl SpecProperties {
    pub(crate) fn get(&self, property: &Property) -> Option<&String> {
        self.properties.get(match property {
            Property::Translator => "translator",
            Property::File => "file",
        })
    }
}

pub(crate) fn extract_properties(tokens: TokenStream) -> syn::Result<(SpecProperties, TokenStream)> {
    let mut tokens_iter = tokens.into_iter().peekable();
    let mut properties = FxHashMap::default();

    let mut matched = false;
    if let Some(TokenTree::Group(group)) = tokens_iter.peek() {
        matched = true;
        let mut tokens_iter = group.stream().into_iter();
        while let Some(prop_name_token) = tokens_iter.next() {
            let prop_name = match &prop_name_token {
                TokenTree::Ident(ident) => ident.to_string(),
                _ => return Err(build_error(&prop_name_token, "property name expected")),
            };

            if properties.contains_key(&prop_name) {
                return Err(build_error(&prop_name_token, "property already defined"));
            }

            let eq_token = tokens_iter.next();
            if !matches!(&eq_token, Some(TokenTree::Punct(p)) if p.as_char() == '=') {
                return Err(build_error(&eq_token.unwrap_or(prop_name_token), "'=' expected"));
            }

            let value_token = tokens_iter.next();
            let prop_value = match value_token {
                Some(TokenTree::Literal(literal)) => literal.to_string(),
                _ => return Err(build_error(&value_token.unwrap_or(eq_token.unwrap()), "property value expected")),
            };

            if let Some(comma_token) = tokens_iter.next() {
                if !matches!(&comma_token, TokenTree::Punct(p) if p.as_char() == ',') {
                    return Err(build_error(&comma_token, "',' expected"));
                }
            }

            properties.insert(prop_name.to_ascii_lowercase(), prop_value);
        }
    }

    if matched {
        tokens_iter.next();
    }

    Ok((SpecProperties {properties}, tokens_iter.collect::<TokenStream>()))
}

fn build_error(token: &TokenTree, msg: &str) -> syn::Error {
    syn::Error::new(token.span(), msg)
}