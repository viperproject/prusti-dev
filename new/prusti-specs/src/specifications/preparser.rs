use proc_macro2::{Delimiter, Group, Spacing, Span, TokenStream, TokenTree, Ident, };
use std::collections::VecDeque;
use std::mem;
use syn::parse::{ParseBuffer, ParseStream, Parse};
use syn::{self, Token, PatType, Pat, Error};
use quote::ToTokens;

use super::common;
use crate::specifications::common::AssertionKind::ForAll;
use crate::specifications::common::{ForAllVars, TriggerSet, Trigger};

pub type AssertionWithoutId = common::Assertion<(), syn::Expr, common::Arg>;
pub type ExpressionWithoutId = common::Expression<(), syn::Expr>;

#[derive(Debug)]
struct ParserStream {
    last_span: Span,
    tokens: VecDeque<TokenTree>,
}

impl ParserStream {
    fn empty() -> Self {
        Self {
            tokens: VecDeque::new(),
            last_span: Span::call_site(),
        }
    }
    fn from_token_stream(tokens: TokenStream) -> Self {
        let token_queue: VecDeque<_> = tokens.into_iter().collect();
        Self {
            tokens: token_queue,
            last_span: Span::call_site(),
        }
    }
    fn last_span(&self) -> Span {
        self.last_span
    }
    fn is_empty(&self) -> bool {
        self.tokens.is_empty()
    }
    fn pop(&mut self) -> Option<TokenTree> {
        if let Some(token) = self.tokens.pop_front() {
            self.last_span = token.span();
            Some(token)
        } else {
            None
        }
    }
    /// Check if the input starts with the keyword and if yes consume it.
    fn check_and_consume_keyword(&mut self, keyword: &str) -> bool {
        if let Some(TokenTree::Ident(ident)) = self.tokens.front() {
            if ident.to_string() == keyword {
                self.pop();
                return true;
            }
        }
        false
    }
    /// Check if the input starts with the operator.
    fn peek_operator(&self, operator: &str) -> bool {
        for (i, c) in operator.char_indices() {
            if let Some(TokenTree::Punct(punct)) = self.tokens.get(i) {
                if punct.as_char() != c {
                    return false;
                }
                if i + 1 < operator.len() && punct.spacing() != Spacing::Joint {
                    return false;
                }
            } else {
                return false;
            }
        }
        true
    }
    /// Check whether the input starts an operator.
    fn peek_any_operator(&self) -> bool {
        self.peek_operator("==>") || self.peek_operator("&&")
    }
    /// Check if the input starts with the operator and if yes consume it.
    fn check_and_consume_operator(&mut self, operator: &str) -> bool {
        if !self.peek_operator(operator) {
            return false;
        }
        for _ in operator.chars() {
            self.pop();
        }
        true
    }
    /// Check if we have a nested assertion here.
    fn check_nested_assertion(&mut self) -> Option<Group> {
        if let Some(TokenTree::Group(group)) = self.tokens.front() {
            if group.delimiter() == Delimiter::Parenthesis {
                if let Some(TokenTree::Group(group)) = self.pop() {
                    return Some(group);
                } else {
                    unreachable!();
                }
            }
        }
        None
    }

    fn parse_identifier(&mut self) -> Option<Ident> {
        if let Some(TokenTree::Ident(ident)) = self.tokens.front() {
            if let Some(TokenTree::Ident(ident)) = self.pop() {
                return Some(ident);
            }
        }
        None
    }

    fn create_stream_until(&mut self, operator: &str) -> TokenStream {
        let mut stream = TokenStream::new();
        let mut t = vec![];
        while !self.peek_operator(operator) && !self.is_empty() {
            t.push(self.pop().unwrap());
        }
        stream.extend(t.into_iter());
        stream
    }

    fn create_stream(&mut self) -> TokenStream {
        let mut stream = TokenStream::new();
        let mut t = vec![];
        while !self.is_empty() {
            t.push(self.pop().unwrap());
        }
        stream.extend(t.into_iter());
        stream
    }
}

#[derive(Debug)]
struct OneArg {
    name: syn::Ident,
    colon: Token![:],
    typ: syn::Type
}

impl Parse for OneArg {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Self{
            name: input.parse()?,
            colon: input.parse()?,
            typ: input.parse()?
        })
    }
}

#[derive(Debug)]
struct AllArgs {
    args: syn::punctuated::Punctuated<OneArg, Token![,]>
}

impl Parse for AllArgs {
    fn parse(input: ParseStream) -> syn::Result<Self>{
        let parsed: syn::punctuated::Punctuated<OneArg, Token![,]> = input.parse_terminated(OneArg::parse)?;
        Ok(Self{
            args: parsed
        })
    }
}

pub struct Parser {
    input: ParserStream,
    conjuncts: Vec<AssertionWithoutId>,
    expr: Vec<TokenTree>,
    previous_expression_nested: bool,
}

impl Parser {
    pub fn new(tokens: TokenStream) -> Self {
        let mut input = ParserStream::from_token_stream(tokens);
        Self {
            input: input,
            conjuncts: Vec::new(),
            expr: Vec::new(),
            previous_expression_nested: false,
        }
    }

    pub fn extract_assertion(&mut self) -> syn::Result<AssertionWithoutId> {
        while !self.input.is_empty() {
            if self.input.check_and_consume_operator("&&") {
                // convert the current expression into a conjunct if it was not nested
                // (and thus already resolved)
                if !self.previous_expression_nested {
                    self.convert_expr_into_conjunct()?;
                }
            }

            else if self.input.check_and_consume_operator("==>") {
                if !self.previous_expression_nested {
                    self.convert_expr_into_conjunct()?;
                }
                let mut parser = Parser {
                    input: mem::replace(&mut self.input, ParserStream::empty()),
                    conjuncts: Vec::new(),
                    expr: Vec::new(),
                    previous_expression_nested: false,
                };
                let lhs = self.conjuncts_to_assertion()?;
                let rhs = parser.extract_assertion()?;
                return Ok(AssertionWithoutId{
                    kind: Box::new(common::AssertionKind::Implies(lhs, rhs))
                });
            }

            else if self.input.check_and_consume_keyword("forall") {
                if let Some(group) = self.input.check_nested_assertion() {
                    let mut stream = ParserStream::from_token_stream(group.stream());

                    // parse head
                    stream.check_and_consume_operator("|");
                    let token_stream = stream.create_stream_until("|");
                    let all_args: AllArgs = syn::parse2(token_stream)?;
                    stream.check_and_consume_operator("|");

                    let mut vars = vec![];
                    for var in all_args.args {
                        vars.push(common::Arg {
                            typ: var.typ,
                            name: var.name
                        })
                    }

                    // parse body
                    let token_stream = stream.create_stream_until(",");
                    let mut parser = Parser::new(token_stream);
                    let body = parser.extract_assertion()?;

                    // parse triggers (check if they are present at all)
                    if stream.peek_operator(",") {
                        stream.check_and_consume_operator(",");
                        stream.check_and_consume_keyword("triggers");
                        stream.check_and_consume_operator("=");
                        let token_stream = stream.create_stream();
                        let arr: syn::ExprArray = syn::parse2(token_stream)?;
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
                            }
                            else {
                                panic!("parse error");
                            }
                        }

                        return Ok(AssertionWithoutId {
                            kind: Box::new(common::AssertionKind::ForAll(
                                ForAllVars {
                                    id: (),
                                    vars
                                },
                                TriggerSet(vec_of_triggers),
                                body,
                            ))
                        })
                    }
                    else{
                        return Ok(AssertionWithoutId {
                            kind: Box::new(common::AssertionKind::ForAll(
                                ForAllVars {
                                    id: (),
                                    vars
                                },
                                TriggerSet(vec![]),
                                body,
                            ))
                        })
                    }
                }
            }

            else if let Some(group) = self.input.check_nested_assertion() {
                if self.expr.is_empty() && (self.input.is_empty() || self.input.peek_any_operator()) {
                    let mut parser = Parser::new(group.stream());
                    let conjunct = parser.extract_assertion()?;

                    if let common::AssertionKind::Expr(expr) = *conjunct.kind {
                        // the expression is just a plain expression, and therefore can be extended
                        let stream = expr.expr.to_token_stream();
                        self.expr.extend(stream.into_iter());
                    }
                    else{
                        // the expression is a conjunction, and therefore is pushed to the result
                        self.previous_expression_nested = true;
                        self.conjuncts.push(conjunct);
                    }
                }
                else {
                    self.expr.push(TokenTree::Group(group));
                }
            }
            else{
                let token = self.input.pop().unwrap();
                self.expr.push(token);
            }
        }

        if !self.expr.is_empty() {
            self.convert_expr_into_conjunct();
        }
        self.conjuncts_to_assertion()
    }

    fn conjuncts_to_assertion(&mut self) -> syn::Result<AssertionWithoutId> {
        let mut conjuncts = mem::replace(&mut self.conjuncts, Vec::new());
        if conjuncts.len() == 1 {
            let conjunct = conjuncts.pop().unwrap();
            if let common::AssertionKind::Expr(expr) = *conjunct.kind {
                Ok(AssertionWithoutId{
                    kind: Box::new(common::AssertionKind::Expr(expr))
                })
            }
            else{
                unreachable!();
            }
        }
        else{
            Ok(AssertionWithoutId{
                kind: Box::new(common::AssertionKind::And(conjuncts))
            })
        }
    }

    fn convert_expr_into_conjunct(&mut self) -> syn::Result<()> {
        let expr = self.expr.clone();
        let mut token_stream = TokenStream::new();
        token_stream.extend(expr.into_iter());
        self.expr.clear();

        let expr = ExpressionWithoutId {
            spec_id: common::SpecificationId::dummy(),
            id: (),
            expr: syn::parse2(token_stream)?,
        };
        self.conjuncts.push(AssertionWithoutId{
            kind: Box::new(common::AssertionKind::Expr(expr))
        });
        Ok(())
    }

    fn missing_assertion_error(&self) -> syn::Error {
        syn::Error::new(self.input.last_span(), "missing assertion")
    }
}
