/// The preparser parses Prusti into an AST

use proc_macro2::{Span, TokenStream, TokenTree};
use std::collections::VecDeque;
use syn::parse::{ParseStream, Parse};
use syn::{Token, Error};
use syn::spanned::Spanned;
use quote::quote;

use super::common;
use crate::specifications::common::{ForAllVars, SpecEntailmentVars, TriggerSet, Trigger};

pub type AssertionWithoutId = common::Assertion<(), syn::Expr, Arg>;
pub type PledgeWithoutId = common::Pledge<(), syn::Expr, Arg>;
pub type ExpressionWithoutId = common::Expression<(), syn::Expr>;

/// The representation of an argument to `forall` (for example `a: i32`)
#[derive(Debug, Clone)]
pub struct Arg {
    pub name: syn::Ident,
    pub typ: syn::Type
}
impl Parse for Arg {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let name = input.parse()?;
        input.parse::<Token![:]>()?;
        let typ = input.parse()?;
        Ok(Self{
            name,
            typ
        })
    }
}

#[derive(Debug)]
struct ForAllArgs {
    args: syn::punctuated::Punctuated<Arg, Token![,]>
}
impl Parse for ForAllArgs {
    fn parse(input: ParseStream) -> syn::Result<Self>{
        let parsed: syn::punctuated::Punctuated<Arg, Token![,]> = input.parse_terminated(Arg::parse)?;
        Ok(Self{
            args: parsed
        })
    }
}

#[derive(Debug)]
struct SpecEntArgs {
    args: syn::punctuated::Punctuated<Arg, Token![,]>
}
impl Parse for SpecEntArgs {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let parsed: syn::punctuated::Punctuated<Arg, Token![,]> = input.parse_terminated(Arg::parse)?;
        Ok(Self{
            args: parsed
        })
    }
}

pub struct Parser {
    /// Tokens yet to be consumed
    tokens: VecDeque<TokenTree>,
    /// Span of the last seen token
    last_span: Span
}

impl Parser {
    /// initializes the parser with a TokenStream
    pub fn from_token_stream(tokens: TokenStream) -> Self {
        Self {
            tokens: tokens.into_iter().collect(),
            last_span: Span::call_site(),
        }
    }
    /// Creates a single Prusti assertion from the input and returns it.
    pub fn extract_assertion(&mut self) -> syn::Result<AssertionWithoutId> {
        let expr = self.parse_prusti()?;
        if let Some(_) = self.pop() {
            Err(syn::Error::new(self.last_span, "unexpected token"))
        } else {
            Ok(expr)
        }
    }
    /// Create a pledge from the input
    pub fn extract_pledge(&mut self) -> syn::Result<PledgeWithoutId> {
        unimplemented!("parsing of whole pledges isn't implemented yet");
    }
    /// Create the rhs of a pledge from the input
    pub fn extract_pledge_rhs_only(&mut self) -> syn::Result<PledgeWithoutId> {
        unimplemented!("parsing of pledge rhses isn't implemented yet");
    }

    /// Parse a prusti expression
    fn parse_prusti(&mut self) -> syn::Result<AssertionWithoutId> {
        let lhs = self.parse_conjunction()?;
        if self.consume_operator("==>") {
            let rhs = self.parse_prusti()?;
            Ok(AssertionWithoutId {
                kind: box common::AssertionKind::Implies(lhs, rhs)
            })
        } else {
            Ok(lhs)
        }
    }
    fn parse_conjunction(&mut self) -> syn::Result<AssertionWithoutId> {
        let mut conjuncts = vec![self.parse_entailment()?];
        while self.consume_operator("&&") {
            conjuncts.push(self.parse_entailment()?);
        }
        if conjuncts.len() == 1 {
            Ok(conjuncts.pop().unwrap())
        } else {
            Ok(AssertionWithoutId {
                kind: box common::AssertionKind::And(conjuncts)
            })
        }
    }
    fn parse_entailment(&mut self) -> syn::Result<AssertionWithoutId> {
        if self.peek_operator("(") || self.peek_keyword("forall") {
            self.parse_primary()
        } else {
            let lhs = self.parse_rust()?;
            if self.consume_operator("|=") {

                let vars = if self.consume_operator("|") {
                    let arg_tokens = self.create_stream_until("|");
                    let all_args: SpecEntArgs = syn::parse2(arg_tokens)?;
                    if !self.consume_operator("|") {
                        return Err(self.error_expected("`|`"));
                    }
                    all_args.args.into_iter()
                                 .map(|var| Arg { typ: var.typ, name: var.name })
                                 .collect()
                } else {
                    vec![]
                };
    
                if !self.consume_operator("[") {
                    return Err(self.error_expected("`[`"));
                }
    
                let mut pres = vec![];
                let mut posts = vec![];
                while !self.peek_operator("]") && !self.tokens.is_empty() {
                    if self.consume_keyword("requires") {
                        if !self.consume_operator("(") { // TODO: expect group to recursively parse after this
                            return Err(self.error_expected("`(`"));
                        }
                        pres.push(self.parse_prusti()?);
                        if !self.consume_operator(")") {
                            return Err(self.error_expected("`)`"));
                        }
                    } else if self.consume_keyword("ensures") {
                        if !self.consume_operator("(") {
                            return Err(self.error_expected("`(`"));
                        }
                        posts.push(self.parse_prusti()?);
                        if !self.consume_operator(")") {
                            return Err(self.error_expected("`)`"));
                        }
                    } else {
                        return Err(self.error_expected("`requires` or `ensures`"));
                    }
                }
    
                if !self.consume_operator("]") {
                    return Err(self.error_expected("`]`"));
                }
    
                Ok(AssertionWithoutId {
                    kind: Box::new(common::AssertionKind::SpecEntailment {
                        closure: lhs,
                        arg_binders: SpecEntailmentVars {
                            spec_id: common::SpecificationId::dummy(),
                            pre_id: (),
                            post_id: (),
                            args: vars,
                            result: Arg { name: syn::Ident::new("result", Span::call_site()),
                                          typ: syn::parse2(quote! { i32 }).unwrap() },
                        },
                        pres,
                        posts,
                    })
                })
            } else {
                Ok(AssertionWithoutId {
                    kind: box common::AssertionKind::Expr(lhs)
                })
            }
        }
    }

    fn parse_primary(&mut self) -> syn::Result<AssertionWithoutId> {
        if self.consume_operator("(") {
            let retval = self.parse_prusti()?;
            if !self.consume_operator(")") {
                return Err(self.error_expected("`)`"));
            }
            Ok(retval)
        } else if self.consume_keyword("forall") {
            if !self.consume_operator("(") {
                return Err(self.error_expected("`(`"));
            }

            if !self.consume_operator("|") {
                return Err(self.error_expected("`|`"));
            }
            let arg_tokens = self.create_stream_until("|");
            if arg_tokens.is_empty() {
                return Err(self.error_no_quantifier_arguments());
            }
            let all_args: ForAllArgs = syn::parse2(arg_tokens)?;
            if !self.consume_operator("|") {
                return Err(self.error_expected("`|`"));
            }
            let vars: Vec<Arg> =
                all_args.args.into_iter()
                             .map(|var| Arg { typ: var.typ, name: var.name })
                             .collect();

            let body = self.parse_prusti()?;

            let mut trigger_set = TriggerSet(vec![]);

            if self.consume_operator(",") {
                if !self.consume_keyword("triggers") {
                    return Err(self.error_expected("`triggers`"));
                }
                if !self.consume_operator("=") {
                    return Err(self.error_expected("`=`"));
                }

                let arr_tokens = self.create_stream_until(")"); // TODO: recursively parse group
                let arr: Result<syn::ExprArray, Error> = syn::parse2(arr_tokens);
                match arr {
                    Ok(arr) => {
                        let mut vec_of_triggers = vec![];
                        for item in arr.elems {
                            if let syn::Expr::Tuple(tuple) = item {
                                vec_of_triggers.push(
                                    Trigger(tuple.elems
                                        .into_iter()
                                        .map(|x| ExpressionWithoutId {
                                            id: (),
                                            spec_id: common::SpecificationId::dummy(),
                                            expr: x })
                                        .collect()
                                    )
                                );
                            } else {
                                return Err(self.error_expected_tuple(item.span()));
                            }
                        }

                        trigger_set = TriggerSet(vec_of_triggers);
                    }
                    Err(err) => return Err(self.error_expected_tuple(err.span()))
                }
            }

            if !self.consume_operator(")") {
                return Err(self.error_expected("`)`"));
            }

            Ok(AssertionWithoutId {
                kind: box common::AssertionKind::ForAll(
                    ForAllVars {
                        spec_id: common::SpecificationId::dummy(),
                        id: (),
                        vars
                    },
                    trigger_set,
                    body,
                )
            })
        } else {
            Err(self.error_expected("`(` or `forall`"))
        }
    }

    fn parse_rust(&mut self) -> syn::Result<ExpressionWithoutId> {
        let mut t = vec![];
        let mut paren_nesting = 0;

        while (paren_nesting > 0 ||
               (!self.peek_operator("|=") &&
                !self.peek_operator("&&") &&
                !self.peek_operator("==>") &&
                !self.peek_operator(")"))) &&
              !self.tokens.is_empty() {
            if self.peek_operator("(") {
                paren_nesting += 1;
            } else if self.peek_operator(")") {
                paren_nesting -= 1;
            }
            t.push(self.pop().unwrap());
        }
        let mut stream = TokenStream::new();
        stream.extend(t.into_iter());
        Ok(ExpressionWithoutId {
            spec_id: common::SpecificationId::dummy(),
            id: (),
            expr: syn::parse2(stream)?,
        })
    }

    /// does the input start with this operator?
    fn peek_operator(&self, operator: &str) -> bool {
        for (i, c) in operator.char_indices() {
            if let Some(TokenTree::Punct(punct)) = self.tokens.get(i) {
                if punct.as_char() != c {
                    return false;
                }
            } else {
                return false;
            }
        }
        true
    }
    /// does the input start with this keyword?
    fn peek_keyword(&self, keyword: &str) -> bool {
        if let Some(TokenTree::Ident(ident)) = self.tokens.front() {
            if ident == keyword {
                return true;
            }
        }
        false
    }
    /// consume the operator if it is next in the stream
    fn consume_operator(&mut self, operator: &str) -> bool {
        if !self.peek_operator(operator) {
            return false;
        }
        let mut span: Option<Span> = None;
        for _ in operator.chars() {
            let character = self.tokens.pop_front().unwrap();
            if let Some(maybe_span) = span {
                span = maybe_span.join(character.span());
            } else {
                span = Some(character.span());
            }
        }
        self.last_span = span.unwrap();
        true
    }
    /// consume the keyword if it is next in the stream
    fn consume_keyword(&mut self, keyword: &str) -> bool {
        if !self.peek_keyword(keyword) {
            return false;
        }
        let mut span: Option<Span> = None;
        for _ in keyword.chars() {
            let character = self.tokens.pop_front().unwrap();
            if let Some(maybe_span) = span {
                span = maybe_span.join(character.span());
            } else {
                span = Some(character.span());
            }
        }
        self.last_span = span.unwrap();
        true
    }
    /// pop a character - not a token!
    fn pop(&mut self) -> Option<TokenTree> {
        if let Some(token) = self.tokens.pop_front() {
            self.last_span = token.span();
            Some(token)
        } else {
            None
        }
    }
    /// pop tokens into a new stream for syn2 until the given operator character
    fn create_stream_until(&mut self, delimiter: &str) -> TokenStream {
        let mut t = vec![];
        while !self.peek_operator(delimiter) && !self.tokens.is_empty() {
            t.push(self.pop().unwrap());
        }
        let mut stream = TokenStream::new();
        stream.extend(t.into_iter());
        stream
    }
    /// complain about expecting a token
    fn error_expected(&self, what: &str) -> syn::Error {
        syn::Error::new(self.last_span, format!("expected {}", what))
    }
    fn error_no_quantifier_arguments(&self) -> syn::Error {
        syn::Error::new(self.last_span, "a quantifier must have at least one argument")
    }
    fn error_expected_tuple(&self, span: Span) -> syn::Error {
        syn::Error::new(span, "`triggers` must be an array of tuples containing Rust expressions")
    }
}
