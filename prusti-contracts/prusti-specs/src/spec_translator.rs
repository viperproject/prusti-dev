use std::collections::BTreeMap;

use itertools::Itertools;
use proc_macro2::{Span, TokenStream, TokenTree};
use quote::ToTokens;

use crate::{parse_quote_spanned, rewriter::SpecItemType};

use super::properties::{Property, SpecProperties};

pub(crate) fn build_translator <'a>(
    properties: &'a SpecProperties,
) -> Option<Box<dyn SpecTranslator + 'a>> {
    match properties.get(&Property::Translator) {
        Some(translator) => build_translator_inner(properties, translator),
        None => None
    }
}

fn build_translator_inner<'a>(properties: &'a SpecProperties, translator: &str) -> Option<Box<dyn SpecTranslator + 'a>> {
    let translator_data = TranslatorData {
        _file: properties.get(&Property::File).map(|x| x.as_str())
    };
    if translator.eq_ignore_ascii_case("\"verifast\"") {
        Some(Box::new(VeriFastTranslator(translator_data)))
    } else {
        eprintln!("Warning: Unsupported translator: {}", translator);
        None
    }
}

pub(crate) trait SpecTranslator {
    fn translate_spec(&self, span: Span, kind: SpecItemType, spec: TokenStream) -> syn::Result<Vec<syn::Attribute>>;
}

struct TranslatorData<'a> {
    _file: Option<&'a str>
}

#[derive(Copy, Clone)]
enum AssertionKind {
    Pre, Post
}

impl From<SpecItemType> for AssertionKind {
    fn from(spec_item_type: SpecItemType) -> Self {
        match spec_item_type {
            SpecItemType::Precondition => AssertionKind::Pre,
            SpecItemType::Postcondition => AssertionKind::Post,
            _ => panic!("Invalid spec item type for path state: {:?}", spec_item_type)
        }
    }
}

struct VeriFastTranslator<'a>(TranslatorData<'a>);

struct VerifastTranslatorContext {
    source: Vec<TokenTree>,
    pos: usize,
    pre_path_permission_conjunctions: BTreeMap<String, String>,
    post_path_permission_conjunctions: BTreeMap<String, String>,
    assertion_parts: Vec<String>,
}

impl VerifastTranslatorContext {
    fn new(source: Vec<TokenTree>) -> Self {
        VerifastTranslatorContext {
            source,
            pos: 0,
            pre_path_permission_conjunctions: BTreeMap::new(),
            post_path_permission_conjunctions: BTreeMap::new(),
            assertion_parts: Vec::new(),
        }
    }

    fn translate(self, span: Span, path_state_type: AssertionKind) -> syn::Result<Vec<syn::Attribute>> {
        self.parse(path_state_type)?.generate_result(span, path_state_type)
    }
    
    fn parse(mut self, path_state_type: AssertionKind) -> syn::Result<Self> {
        while self.pos < self.source.len() {
            self.pos += 1;
            let next_token = match (&self.source[self.pos - 1], self.source.get(self.pos)) {
                (
                    TokenTree::Punct(p1),
                    Some(TokenTree::Punct(p2))
                ) => {
                    self.pos += 1;
                    Some(match (p1.as_char(), p2.as_char()) {
                        ('&', '&') => "&*&",
                        ('=', '=') => "==",
                        _ => todo!()
                    }.to_owned())
                }
                (TokenTree::Punct(p), _) if matches!(p.as_char(), '+' | '-' | '*' | '/') => {
                    Some(p.to_string())
                }
                (TokenTree::Literal(l), _) => match syn::parse2::<syn::Lit>(l.to_token_stream())? {
                    syn::Lit::Int(i) => Some(i.to_string()),
                    _ => return Err(syn::Error::new(l.span(), "Unsupported literal type"))
                },
                (TokenTree::Ident(ident), _) if matches!(ident.to_string().as_str(), "true" | "false") => Some(ident.to_string()),
                (TokenTree::Ident(ident), Some(TokenTree::Group(group))) if ident.to_string().as_str() == "old" => {
                    // TODO Handle the case of more complex old expressions
                    self.pos += 1;
                    let parsed_subexpression_context =
                        Self::new(group.stream().into_iter().collect())
                        .parse(AssertionKind::Pre)?;
                    self.extend(parsed_subexpression_context);   
                    None
                }
                (TokenTree::Ident(ident), _) => {
                    Some(self.parse_path(path_state_type, &ident.clone()))
                }
                _ => todo!()
            };

            if let Some(next_token) = next_token {
                self.assertion_parts.push(next_token);
            }
        }
        Ok(self)
    }
    
    fn parse_path(&mut self, path_state_type: AssertionKind, start: &proc_macro2::Ident) -> String {
        let mut path = vec![start];
        loop {
            match (self.source.get(self.pos), self.source.get(self.pos + 1)) {
                (Some(TokenTree::Punct(p)), Some(TokenTree::Ident(ident))) if p.as_char() == '.' => {
                    self.pos += 2;
                    path.push(ident);
                }
                _ => break
            }
        }

        if path.len() == 1 {
            path[0].to_string()
        } else {
            let value_identifier = format!("{}{}", map_to_prefix(path_state_type), path.iter().join("_"));
            let permission_conjunctions = match path_state_type {
                AssertionKind::Pre => &mut self.pre_path_permission_conjunctions,
                AssertionKind::Post => &mut self.post_path_permission_conjunctions
            };

            if !permission_conjunctions.contains_key(&value_identifier) {
                permission_conjunctions.insert(value_identifier.clone(), path.iter().join("->"));
            } 
            value_identifier
        }
    }

    fn extend(&mut self, other: Self) {
        self.pre_path_permission_conjunctions.extend(other.pre_path_permission_conjunctions.into_iter());
        self.post_path_permission_conjunctions.extend(other.post_path_permission_conjunctions.into_iter());
        self.assertion_parts.extend(other.assertion_parts.into_iter());
    }

    fn generate_permission_conjunctions(&self, permission_conjunctions: &BTreeMap<String, String>) -> String {
        permission_conjunctions.iter()
            .map(|(key, value)| format!("{} |-> ?{}", value, key))
            .join(" &*& ")
    }

    fn generate_result(mut self, span: Span, path_state_type: AssertionKind) -> syn::Result<Vec<syn::Attribute>> {
        let parsed_post_permission_conjunctions = self.generate_permission_conjunctions(&self.post_path_permission_conjunctions);
        let mut parsed_pre_permission_conjunctions = self.generate_permission_conjunctions(&self.pre_path_permission_conjunctions);
        if parsed_pre_permission_conjunctions.is_empty() {
            parsed_pre_permission_conjunctions = "true".to_owned();
        }

        if self.assertion_parts.is_empty() {
            self.assertion_parts.push("true".to_owned());
        }

        let assertion = self.assertion_parts.into_iter().join(" ");

        Ok(vec![
            parse_quote_spanned! {span=>
                #[prusti::verifast_precall_field_bindings = #parsed_pre_permission_conjunctions]
            },
            parse_quote_spanned! {span=>
                #[prusti::verifast_postcall_field_bindings = #parsed_post_permission_conjunctions]
            },
            match path_state_type {
                AssertionKind::Pre => parse_quote_spanned! {span=>
                    #[prusti::verifast_precondition = #assertion]
                },
                AssertionKind::Post => parse_quote_spanned! {span=>
                    #[prusti::verifast_postcondition = #assertion]
                }
            }
        ])
    }
}

impl SpecTranslator for VeriFastTranslator<'_> {
    // TODO Add specced function item parameter:
    fn translate_spec(&self, span: Span, kind: SpecItemType, spec: TokenStream) -> syn::Result<Vec<syn::Attribute>> {
        VerifastTranslatorContext::new(spec.into_iter().collect())
            .translate(span, kind.into())
    }
}

fn map_to_prefix(kind: AssertionKind) -> String {
    match kind {
        AssertionKind::Pre => "_pre_",
        AssertionKind::Post => "_post_",
    }.to_owned()
}

#[cfg(test)]
mod tests {
    use super::*;
    use proc_macro2::TokenStream;
    use syn::{Lit, MetaNameValue};
    
    #[test]
    fn test_empty() {
        test_post("", "", "true");
    }

    #[test]
    fn test_true() {
        test_post("true", "", "true");
    }

    #[test]
    fn test_identity_function() {
        test_post("result == a", "", "result == a")
    }

    #[test]
    fn test_simple_path() {
        test_post(
            "a.b.c == 1",
            "a->b->c |-> ?_post_a_b_c",
            "_post_a_b_c == 1"
        );
    }

    #[test]
    fn test_complex_conjunction() {
        test_post(
            "a.b.c == 3 && a.d == 2 + a.b.c",
            "a->b->c |-> ?_post_a_b_c &*& a->d |-> ?_post_a_d",
            "_post_a_b_c == 3 &*& _post_a_d == 2 + _post_a_b_c"
        );
    }

    #[test]
    fn test_complex_conjunction_with_old() {
        test_post_with_old(
            "p.x == old(p.y) && p.y == old(p.x)",
            "p->x |-> ?_pre_p_x &*& p->y |-> ?_pre_p_y",
            
            "p->x |-> ?_post_p_x &*& p->y |-> ?_post_p_y",
            "_post_p_x == _pre_p_y &*& _post_p_y == _pre_p_x", 
        );
    }

    #[test]
    fn test_complex_old_expression() {
        test_post_with_old(
            "p.x == old(p.y + p.x) && p.y == old(p.y - p.x) && result == p.x * p.y",
            "p->x |-> ?_pre_p_x &*& p->y |-> ?_pre_p_y",
            "p->x |-> ?_post_p_x &*& p->y |-> ?_post_p_y",
            "_post_p_x == _pre_p_y + _pre_p_x &*& _post_p_y == _pre_p_y - _pre_p_x &*& result == _post_p_x * _post_p_y",
        );
    }

    fn test_post(prusti: &str, post_call_bindings: &str, postcondition: &str) {
        test_post_with_old(prusti, "true", post_call_bindings, postcondition);
    }

    fn test_post_with_old(pusti: &str, pre_call_bindings: &str, post_call_bindings: &str, postcondition: &str) {
        let translator = VeriFastTranslator(TranslatorData { _file: None });
        let token_stream: TokenStream = syn::parse_str(pusti).expect("Failed to parse string into TokenStream");
        let span = Span::call_site();
        let result = translator.translate_spec(span, SpecItemType::Postcondition, token_stream).unwrap();
        assert_meta_value_attribute(&result[0], pre_call_bindings);
        assert_meta_value_attribute(&result[1], post_call_bindings);
        assert_meta_value_attribute(&result[2], postcondition);
    }

    fn assert_meta_value_attribute(attribute: &syn::Attribute, value: &str) {
        if let Ok(syn::Meta::NameValue(MetaNameValue{
            path: _,
            eq_token: _,
            lit: Lit::Str(string_literal) 
        })) = attribute.parse_meta() {
            assert_eq!(string_literal.value().as_str(), value)
        } else {
            panic!("{:?} is not a name value meta attribute.", attribute);
        }
    }
}