/// The preparser parses Prusti into an AST

use proc_macro2::{Span, TokenStream, TokenTree, Delimiter};
use std::collections::VecDeque;
use syn::parse::{ParseStream, Parse};
use syn::Token;
use syn::spanned::Spanned;
use quote::quote;

use super::common;
use crate::specifications::common::{QuantifierVars, SpecEntailmentVars, TriggerSet, Trigger};

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

/// The representation of all arguments to `forall`
/// (for example `a: i32, b: i32, c: i32`)
#[derive(Debug)]
struct ForAllArgs {
    args: syn::punctuated::Punctuated<Arg, Token![,]>
}
impl Parse for ForAllArgs {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let parsed: syn::punctuated::Punctuated<Arg, Token![,]> = input.parse_terminated(Arg::parse)?;
        Ok(Self {
            args: parsed
        })
    }
}

/// The representation of all arguments to a specification entailment
/// (for example `a: i32, b: i32, c: i32`)
#[derive(Debug)]
struct SpecEntArgs {
    args: syn::punctuated::Punctuated<Arg, Token![,]>
}
impl Parse for SpecEntArgs {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let parsed: syn::punctuated::Punctuated<Arg, Token![,]> = input.parse_terminated(Arg::parse)?;
        Ok(Self {
            args: parsed
        })
    }
}

pub struct Parser {
    /// Tokens yet to be consumed
    tokens: VecDeque<TokenTree>,
    /// Span of the last seen token
    last_span: Option<Span>,
    /// Span of the surrounding token
    source_span: Option<Span>,
}

impl Parser {
    /// initializes the parser with a TokenStream
    pub fn from_token_stream(tokens: TokenStream) -> Self {
        Self {
            tokens: tokens.into_iter().collect(),
            last_span: None,
            source_span: None,
        }
    }
    /// initializes the parser with a TokenStream and the last span
    fn from_token_stream_last_span(&self, tokens: TokenStream) -> Self {
        Self {
            tokens: tokens.into_iter().collect(),
            last_span: None,
            source_span: self.last_span,
        }
    }
    /// Creates a single Prusti assertion from the input and returns it.
    pub fn extract_assertion(&mut self) -> syn::Result<AssertionWithoutId> {
        if self.tokens.is_empty() {
            Ok(AssertionWithoutId {
                kind: Box::new(common::AssertionKind::And(vec![]))
            })
        } else {
            if let Some(span) = self.contains_both_and_or(&self.tokens) {
                return Err(self.error_ambiguous_expression(span));
            }

            let expr = self.parse_prusti()?;
            if self.pop().is_some() {
                Err(self.error_unexpected())
            } else {
                Ok(expr)
            }
        }
    }
    /// Create a pledge from the input
    pub fn extract_pledge(&mut self) -> syn::Result<PledgeWithoutId> {
        let pledge = self.parse_pledge()?;
        if self.pop().is_some() {
            Err(self.error_unexpected())
        } else {
            Ok(pledge)
        }
    }
    /// Create the rhs of a pledge from the input
    pub fn extract_pledge_rhs_only(&mut self) -> syn::Result<PledgeWithoutId> {
        let (reference, assertion) = self.parse_pledge_assertion_only()?;
        if self.pop().is_some() {
            Err(self.error_unexpected())
        } else {
            Ok(PledgeWithoutId {
                reference,
                lhs: None,
                rhs: assertion,
            })
        }
    }

    fn parse_pledge(&mut self) -> syn::Result<PledgeWithoutId> {
        let (reference, assertion) = self.parse_pledge_assertion_only()?;
        if self.consume_operator(",") {
            let rhs = self.parse_prusti()?;
            Ok(PledgeWithoutId {
                reference,
                lhs: Some(assertion),
                rhs,
            })
        } else {
            Err(self.error_expected("`,`"))
        }
    }

    fn parse_pledge_assertion_only(&mut self) -> syn::Result<(Option<ExpressionWithoutId>, AssertionWithoutId)> {
        let mut reference = None;
        if self.contains_operator(&self.tokens, "=>") {
            reference = Some(self.parse_rust_until("=>")?);
            self.consume_operator("=>");
        }

        let assertion = self.parse_prusti()?;

        Ok((reference, assertion))
    }

    /// Parse a prusti expression
    fn parse_prusti(&mut self) -> syn::Result<AssertionWithoutId> {
        let lhs = self.parse_conjunction()?;
        if self.consume_operator("==>") {
            let rhs = self.parse_prusti()?;
            Ok(AssertionWithoutId {
                kind: Box::new(common::AssertionKind::Implies(lhs, rhs)),
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
                kind: Box::new(common::AssertionKind::And(conjuncts))
            })
        }
    }
    fn parse_entailment(&mut self) -> syn::Result<AssertionWithoutId> {
        if (self.peek_group(Delimiter::Parenthesis) && !self.is_part_of_rust_expr()) ||
           self.peek_keyword("forall") ||
           self.peek_keyword("exists") {
            self.parse_primary()
        } else {
            let lhs = self.parse_rust_until(",")?;
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

                if let Some(stream) = self.consume_group(Delimiter::Bracket) {
                    self.from_token_stream_last_span(stream).extract_entailment_rhs(lhs, vars)
                } else {
                    Err(self.error_expected("`[`"))
                }
            } else {
                Ok(AssertionWithoutId {
                    kind: Box::new(common::AssertionKind::Expr(lhs))
                })
            }
        }
    }
    fn extract_entailment_rhs(&mut self, lhs: ExpressionWithoutId, vars: Vec<Arg>) ->
            syn::Result<AssertionWithoutId> {
        let mut pres = vec![];
        let mut posts = vec![];
        let mut first = true;
        while !self.tokens.is_empty() {
            if first || self.consume_operator(",") {
                first = false;
                    if self.consume_keyword("requires") {
                        if let Some(stream) = self.consume_group(Delimiter::Parenthesis) {
                            pres.push(self.from_token_stream_last_span(stream).extract_assertion()?);
                        } else {
                            return Err(self.error_expected("`(`"));
                        }
                    } else if self.consume_keyword("ensures") {
                        if let Some(stream) = self.consume_group(Delimiter::Parenthesis) {
                            posts.push(self.from_token_stream_last_span(stream).extract_assertion()?);
                        } else {
                            return Err(self.error_expected("`(`"));
                        }
                    } else {
                        return Err(self.error_expected("`requires` or `ensures`"));
                    }
            } else {
                return Err(self.error_expected("`,`"));
            }
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
    }
    /// parse a paren-delimited expression
    fn parse_primary(&mut self) -> syn::Result<AssertionWithoutId> {
        if let Some(stream) = self.consume_group(Delimiter::Parenthesis) {
            self.from_token_stream_last_span(stream).extract_assertion()
        } else if self.consume_keyword("forall") {
            if let Some(stream) = self.consume_group(Delimiter::Parenthesis) {
                self.from_token_stream_last_span(stream).extract_quantifier_rhs(false)
            } else {
                Err(self.error_expected("`(`"))
            }
        } else if self.consume_keyword("exists") {
            if let Some(stream) = self.consume_group(Delimiter::Parenthesis) {
                self.from_token_stream_last_span(stream).extract_quantifier_rhs(true)
            } else {
                Err(self.error_expected("`(`"))
            }
        } else {
            Err(self.error_expected("`(`, `forall` or `exists`"))
        }
    }
    fn extract_quantifier_rhs(&mut self, exists: bool) -> syn::Result<AssertionWithoutId> {
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

            let arr: syn::ExprArray = syn::parse2(self.create_stream_remaining())
                .map_err(|err| self.error_expected_tuple(err.span()))?;

                let mut vec_of_triggers = vec![];
            for item in arr.elems {
                if let syn::Expr::Tuple(tuple) = item {
                    vec_of_triggers.push(
                        Trigger(tuple.elems
                            .into_iter()
                            .map(|x| ExpressionWithoutId {
                                id: (),
                                spec_id: common::SpecificationId::dummy(),
                                expr: x,
                            })
                            .collect()
                        )
                    );
                } else {
                    return Err(self.error_expected_tuple(item.span()));
                }
            }
            trigger_set = TriggerSet(vec_of_triggers);
        }

        let vars = QuantifierVars {
            spec_id: common::SpecificationId::dummy(),
            id: (),
            vars,
        };
        Ok(AssertionWithoutId {
            kind: if exists {
                Box::new(common::AssertionKind::Exists(vars, trigger_set, body))
            } else {
                Box::new(common::AssertionKind::ForAll(vars, trigger_set, body))
            }
        })
    }

    fn parse_rust_until(&mut self, terminator: &str) -> syn::Result<ExpressionWithoutId> {
        let mut t = vec![];

        while !self.peek_operator("|=") &&
              !self.peek_operator("&&") &&
              !self.peek_operator("==>") &&
              !self.peek_operator(terminator) &&
              !self.tokens.is_empty() {
            t.push(self.pop().unwrap());
        }
        let mut stream = TokenStream::new();
        stream.extend(t.into_iter());

        let cloned: VecDeque<TokenTree> = stream.clone().into_iter().collect();
        if let Some(span) = self.contains_operator_recursive(&cloned, "==>") {
            Err(self.error_no_implies(span))
        } else if cloned.is_empty() {
            Err(self.error_expected("expression"))
        } else {
            Ok(ExpressionWithoutId {
                spec_id: common::SpecificationId::dummy(),
                id: (),
                expr: syn::parse2(stream)?,
            })
        }
    }

    /// is there any non-prusti operator following the first thing?
    fn is_part_of_rust_expr(&mut self) -> bool {
        if let Some(token) = self.tokens.pop_front() {
            let result = !(self.peek_operator("|=") ||
               self.peek_operator("&&") ||
               self.peek_operator("==>") ||
               self.tokens.front().is_none());
            self.tokens.push_front(token);
            result
        } else {
            false
        }
    }
    /// does the given operator appear in the stream at top level
    fn contains_operator(&self, stream: &VecDeque<TokenTree>, operator: &str) -> bool {
        (0..stream.len()).any(|offset: usize| self.peek_operator_stream_offset(stream, operator, offset))
    }
    /// does the given operator appear in the stream anywhere
    fn contains_operator_recursive(&self, stream: &VecDeque<TokenTree>, operator: &str) -> Option<Span> {
        for (offset, token) in stream.iter().enumerate() {
            if self.peek_operator_stream_offset(stream, operator, offset) {
                return Some(self.operator_span_offset(stream, operator, offset));
            }
            if let TokenTree::Group(group) = token {
                let nested_stream: VecDeque<TokenTree> = group.stream().into_iter().collect();
                if let Some(span) = self.contains_operator_recursive(&nested_stream, operator) {
                    return Some(span);
                }
            }
        }
        None
    }
    /// get the span of the peeked operator
    fn operator_span_offset(&self, stream: &VecDeque<TokenTree>, operator: &str, offset: usize) -> Span {
        stream.get(offset).unwrap().span().join(stream.get(offset + operator.len() - 1).unwrap().span()).unwrap()
    }
    /// Check if there is a subexpression (parenthesized or separated by `==>`)
    /// that contains both `&&` and `||`. If yes, set the span to include both
    /// of those operators and everything in between them. This detects
    /// potentially ambiguous subexpressions.
    fn contains_both_and_or(&self, stream: &VecDeque<TokenTree>) -> Option<Span> {
        let mut and_span: Option<Span> = None;
        let mut or_span: Option<Span> = None;

        for (offset, token) in stream.iter().enumerate() {
            if self.peek_operator_stream_offset(stream, "&&", offset) {
                and_span = Some(self.operator_span_offset(stream, "&&", offset));
            } else if self.peek_operator_stream_offset(stream, "||", offset) {
                or_span = Some(self.operator_span_offset(stream, "||", offset));
            } else if self.peek_operator_stream_offset(stream, "==>", offset) {
                and_span = None;
                or_span = None;
            } else if let TokenTree::Group(group) = token {
                if group.delimiter() == Delimiter::Parenthesis {
                    let inner = group.stream().into_iter().collect();
                    let span = self.contains_both_and_or(&inner);
                    if span.is_some() {
                        return span;
                    }
                }
            }

            if let (Some(a_s), Some(o_s)) = (and_span, or_span) {
                return Some(a_s.join(o_s).unwrap());
            }
        }
        None
    }
    /// does the input start with this operator?
    fn peek_operator(&self, operator: &str) -> bool {
        self.peek_operator_stream_offset(&self.tokens, operator, 0)
    }
    /// does the given stream contain this operator?
    fn peek_operator_stream_offset(&self, stream: &VecDeque<TokenTree>, operator: &str, offset: usize) -> bool {
        for (i, c) in operator.char_indices() {
            if let Some(TokenTree::Punct(punct)) = stream.get(i + offset) {
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
    /// does the input start with a group with the given grouping?
    fn peek_group(&self, delimiter: Delimiter) -> bool {
        if let Some(TokenTree::Group(group)) = self.tokens.front() {
            if delimiter == group.delimiter() {
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
        self.last_span = (0..operator.len())
	        .filter_map(|_| self.tokens.pop_front())
	        .map(|character| character.span())
	        .reduce(|span_a, span_b| span_a.join(span_b).unwrap());
        true
    }
    /// consume the keyword if it is next in the stream
    fn consume_keyword(&mut self, keyword: &str) -> bool {
        if !self.peek_keyword(keyword) {
            return false;
        }
        self.last_span = Some(self.tokens.pop_front().unwrap().span());
        true
    }
    /// consume the group if it is next in the stream
    /// produced its TokenStream, if it has one
    fn consume_group(&mut self, delimiter: Delimiter) -> Option<TokenStream> {
        if !self.peek_group(delimiter) {
            return None;
        }
        let token = self.tokens.pop_front().unwrap();
        let span = token.span();
        if let TokenTree::Group(group) = token {
            self.last_span = Some(span);
            Some(group.stream())
        } else {
            None
        }
    }
    /// pop a token - note that punctuation is one token per character
    fn pop(&mut self) -> Option<TokenTree> {
        if let Some(token) = self.tokens.pop_front() {
            self.last_span = Some(token.span());
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
    /// pop tokens into a new stream for syn2 until the given operator character
    fn create_stream_remaining(&mut self) -> TokenStream {
        let mut t = vec![];
        while !self.tokens.is_empty() {
            t.push(self.pop().unwrap());
        }
        let mut stream = TokenStream::new();
        stream.extend(t.into_iter());
        stream
    }
    /// get the span of the blamed token
    fn get_error_span(&self) -> Span {
        if let Some(span) = self.last_span {
            span
        } else if let Some(token) = self.tokens.front() {
            token.span()
        } else if let Some(span) = self.source_span {
            span
        } else {
            Span::call_site()
        }
    }
    /// complain about expecting a token
    fn error_expected(&self, what: &str) -> syn::Error {
        syn::Error::new(self.get_error_span(), format!("expected {}", what))
    }
    fn error_no_quantifier_arguments(&self) -> syn::Error {
        syn::Error::new(self.get_error_span(), "a quantifier must have at least one argument")
    }
    fn error_expected_tuple(&self, span: Span) -> syn::Error {
        syn::Error::new(span, "`triggers` must be an array of tuples containing Rust expressions")
    }
    fn error_unexpected(&self) -> syn::Error {
        syn::Error::new(self.get_error_span(), "unexpected token")
    }
    fn error_no_implies(&self, span: Span) -> syn::Error {
        syn::Error::new(span, "`==>` cannot be part of Rust expression")
    }
    fn error_ambiguous_expression(&self, span: Span) -> syn::Error {
        syn::Error::new(
            span,
            "found `||` and `&&` in the same subexpression. \
            Hint: add parentheses to clarify the evaluation order.")
    }
}
