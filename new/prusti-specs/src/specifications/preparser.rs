use proc_macro2::{Delimiter, Group, Spacing, Span, TokenStream, TokenTree, Ident, };
use std::collections::VecDeque;
use std::mem;
use syn::parse::{ParseBuffer, ParseStream, Parse};
use syn::{self, Token, PatType, Pat, Error};
use quote::ToTokens;

use super::common;
use crate::specifications::common::AssertionKind::ForAll;
use crate::specifications::common::{ForAllVars, TriggerSet, Trigger};
use syn::spanned::Spanned;

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

    fn contains_both_and_or(&mut self) -> bool {
        let tokens = self.tokens.clone();
        let mut contains_and = false;
        let mut contains_or = false;
        let mut and_span: Option<Span> = None;
        let mut or_span: Option<Span> = None;

        while !self.tokens.is_empty() {
            if self.peek_operator("&&") {
                contains_and = true;
                and_span = Some(self.tokens.front().span());
            }
            else if self.peek_operator("||") {
                contains_or = true;
                or_span = Some(self.tokens.front().span());
            }
            else if self.peek_operator("==>") {
                contains_and = false;
                contains_or = false;
            }

            if contains_and && contains_or {
                if let Some(a_s) = and_span {
                    if let Some(o_s) = or_span {
                        self.last_span = a_s.join(o_s).unwrap();
                    }
                }
                return true;
            }
            self.pop();
        }
        self.tokens = tokens;
        return false;
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

        let mut span: Option<Span> = None;
        for _ in operator.chars() {
            self.pop();
            if let Some(maybe_span) = span {
                span = maybe_span.join(self.last_span);
            }
            else {
                span = Some(self.last_span);
            }
        }
        self.last_span = span.unwrap();
        true
    }
    /// Check if we have a nested assertion here.
    fn check_and_consume_parenthesized_block(&mut self) -> Option<Group> {
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

/// The structure to parse Prusti assertions.
///
/// Check common::AssertionKind to see all types of Prusti assertions.
///
/// Each Prusti assertion (`A`) is a Rust expression (`E`) or a `forall` expression.
/// On Prusti assertions, the following operators can be used to create more Prusti assertions:
/// - `A && A` (conjunction)
/// - `A ==> A` (implication)
/// Parentheses can be used as usual.
///
/// The following are also Prusti assertions:
/// `forall(|NAME1: TYPE1, NAME2: TYPE2, ...| A)`
/// `forall(|NAME1: TYPE1, NAME2: TYPE2, ...| A, triggers=[(E, ...), ...])`
///
/// Prusti assertions can only be joined together by `&&` and `==>`, for example the following
/// is not allowed, since `(E ==> E)` is a Prusti assertion:
/// `(E ==> E) || E`
/// However, this is fine, as `&&` is also a Rust operator:
/// `(E && E) && E`
///
/// Having `&&` and `||` in the same subexpression is not allowed to preven ambiguities:
/// `E && E || E`
///
/// However, this is fine, since the implication resolves the ambiguity:
/// (note that both the lhs and rhs of the implication form a Prusti assertion)
/// `E && E ==> E || E`
///
/// Basic usage (`tokens` is of type `proc_macro2::TokenStream`):
/// ```
/// let mut parser = Parser::from_token_stream(tokens);
/// let assertion = parser.extract_assertion()?;
/// ```
pub struct Parser {
    /// The helper to manipulate input.
    input: ParserStream,
    /// Members of the conjunction.
    conjuncts: Vec<AssertionWithoutId>,
    /// Currently being parsed Rust expression.
    expr: Vec<TokenTree>,
    /// A flag to denote whether the previous expression is already resolved (parsed into a conjunct).
    previous_expression_resolved: bool,
    /// A flag to denote that once the current expression finishes, an operator will be expected.
    expected_operator: bool,
    /// A flag to denote that the next token must be an operator.
    expected_only_operator: bool
}

impl Parser {
    pub fn from_token_stream(tokens: TokenStream) -> Self {
        let mut input = ParserStream::from_token_stream(tokens);
        Self {
            input: input,
            conjuncts: Vec::new(),
            expr: Vec::new(),
            previous_expression_resolved: false,
            expected_operator: false,
            expected_only_operator: false
        }
    }

    fn from_parser_stream(input: &mut ParserStream) -> Self {
        Self {
            input: mem::replace(input, ParserStream::empty()),
            conjuncts: Vec::new(),
            expr: Vec::new(),
            previous_expression_resolved: false,
            expected_operator: false,
            expected_only_operator: false
        }
    }

    /// Creates a single Prusti assertion from the input and returns it.
    pub fn extract_assertion(&mut self) -> syn::Result<AssertionWithoutId> {
        if self.input.contains_both_and_or() {
            return Err(self.error_ambiguous_expression());
        }

        while !self.input.is_empty() {
            if self.input.check_and_consume_operator("&&") {

                // handles the case when there is no lhs of the && operator
                if !self.expected_operator {
                    return Err(self.error_expected_assertion());
                }

                // convert the currently being parsed expression into a conjunct if not already
                // done so
                if self.previous_expression_resolved {
                    self.previous_expression_resolved = false;
                }
                else {
                    if self.expr.is_empty() {
                        return Err(self.error_expected_assertion());
                    }
                    if let Err(err) = self.convert_expr_into_conjunct() {
                        return Err(err);
                    }
                }

                // handles the case when there is no rhs of the && operator
                if self.input.is_empty() {
                    return Err(self.error_expected_assertion());
                }

                self.expected_operator = false;
                self.expected_only_operator = false;
            }

            else if self.input.check_and_consume_operator("==>") {

                // handles the case when there is no lhs of the ==> operator
                if !self.expected_operator {
                    return Err(self.error_expected_assertion());
                }

                // convert the currently being parsed expression into a conjunct if not already
                // done so
                if !self.previous_expression_resolved {
                    if self.expr.is_empty() {
                        return Err(self.error_expected_assertion());
                    }
                    if let Err(err) = self.convert_expr_into_conjunct() {
                        return Err(err);
                    }
                }

                // handles the case when there is no rhs of the ==> operator
                if self.input.is_empty() {
                    return Err(self.error_expected_assertion());
                }

                // recursively parse the rhs assertion; note that this automatically handles the
                // operator precedence: implication will be then weaker than conjunction
                let mut parser = Parser::from_parser_stream(&mut self.input);

                let lhs = self.conjuncts_to_assertion();
                if let Err(err) = lhs {
                    return Err(err);
                }

                let rhs = parser.extract_assertion();
                if let Err(err) = rhs {
                    return Err(err);
                }

                return Ok(AssertionWithoutId{
                    kind: Box::new(common::AssertionKind::Implies(lhs.unwrap(), rhs.unwrap()))
                });
            }

            else if self.input.check_and_consume_keyword("forall") {
                if self.expected_operator {
                    return Err(self.error_expected_operator());
                }

                // check whether there is a parenthesized block after forall
                if let Some(group) = self.input.check_and_consume_parenthesized_block() {

                    // construct a ParserStream off of the parenthesized block for further parsing
                    let mut stream = ParserStream::from_token_stream(group.stream());

                    // parse vars
                    if !stream.check_and_consume_operator("|") {
                        return Err(self.error_expected_or());
                    }
                    let token_stream = stream.create_stream_until("|");
                    let all_args: AllArgs = syn::parse2(token_stream)?;
                    if !stream.check_and_consume_operator("|") {
                        return Err(self.error_expected_or());
                    }
                    let mut vars = vec![];
                    for var in all_args.args {
                        vars.push(common::Arg {
                            typ: var.typ,
                            name: var.name
                        })
                    }

                    // parse body
                    let token_stream = stream.create_stream_until(",");
                    let mut parser = Parser::from_token_stream(token_stream);
                    let body = parser.extract_assertion()?;

                    // create triggers in case they are not present
                    let mut trigger_set = TriggerSet(vec![]);

                    // parse triggers (check if they are present at all)
                    if stream.peek_operator(",") {
                        stream.check_and_consume_operator(",");
                        if !stream.check_and_consume_keyword("triggers") {
                            return Err(self.error_expected_triggers());
                        }
                        if !stream.check_and_consume_operator("=") {
                            return Err(self.error_expected_equals());
                        }
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
                                return Err(self.error_expected_tuple());
                            }
                        }

                        trigger_set = TriggerSet(vec_of_triggers);
                    }

                    let conjunct = AssertionWithoutId {
                        kind: Box::new(common::AssertionKind::ForAll(
                            ForAllVars {
                                id: (),
                                vars
                            },
                            trigger_set,
                            body,
                        ))
                    };

                    self.conjuncts.push(conjunct);
                    self.previous_expression_resolved = true;
                    self.expected_only_operator = true;
                    self.expected_operator = true;

                }
                else {
                    return Err(self.error_expected_parenthesis());
                }
            }

            else if let Some(group) = self.input.check_and_consume_parenthesized_block() {
                // handling a parenthesized block
                if self.expected_only_operator {
                    return Err(self.error_expected_operator());
                }

                if self.expr.is_empty() && (self.input.peek_any_operator() || self.input.is_empty()) {
                    // if there is no expression currently being parsed (in which case the
                    // parenthesized block would be a part of it) and there is a Prusti operator
                    // or nothing at all after the parenthesized block, then we might parser
                    // this as a Prusti assertion

                    if self.expected_operator {
                        return Err(self.error_expected_operator());
                    }

                    let mut parser = Parser::from_token_stream(group.stream());
                    let conjunct = parser.extract_assertion();

                    if let Err(err) = conjunct {
                        return Err(err);
                    }

                    let conjunct = conjunct.unwrap();
                    self.conjuncts.push(conjunct);
                    self.previous_expression_resolved = true;
                    self.expected_operator = true;
                }
                else{
                    // if this was not the case, we just parse as a Rust expression and stick
                    // it to any possible already being-parsed expression
                    self.expr.push(TokenTree::Group(group));
                }
            }

            else{
                // if nothing of the above happened, we just continue parsing as a Rust expression
                if self.expected_only_operator {
                    self.input.pop();
                    return Err(self.error_expected_operator());
                }

                let token = self.input.pop().unwrap();
                self.expr.push(token);
                self.expected_operator = true;
            }
        }

        // when the input is parsed, convert the trailing expression into a conjunct (if any)
        if !self.expr.is_empty() {
            if let Err(err) = self.convert_expr_into_conjunct() {
                return Err(err);
            }
        }

        // build a conjunction off of the assertions parsed
        self.conjuncts_to_assertion()
    }

    fn conjuncts_to_assertion(&mut self) -> syn::Result<AssertionWithoutId> {
        let mut conjuncts = mem::replace(&mut self.conjuncts, Vec::new());

        // if there is just one conjunction, don't construct a conjunction and just return it
        // as a single assertion
        if conjuncts.len() == 1 {
            Ok(conjuncts.pop().unwrap())
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

        let maybe_expr = syn::parse2(token_stream);
        if let Err(err) = maybe_expr {
            return Err(err);
        }

        let expr = ExpressionWithoutId {
            spec_id: common::SpecificationId::dummy(),
            id: (),
            expr: maybe_expr.unwrap(),
        };
        self.conjuncts.push(AssertionWithoutId{
            kind: Box::new(common::AssertionKind::Expr(expr))
        });
        Ok(())
    }

    fn error_expected_assertion(&self) -> syn::Error {
        syn::Error::new(self.input.last_span(), "expected Prusti assertion")
    }

    fn error_expected_operator(&self) -> syn::Error {
        syn::Error::new(self.input.last_span(), "expected Prusti operator")
    }

    fn error_expected_parenthesis(&self) -> syn::Error {
        syn::Error::new(self.input.last_span(), "expected `(`")
    }

    fn error_expected_or(&self) -> syn::Error {
        syn::Error::new(self.input.last_span(), "expected `|`")
    }

    fn error_expected_triggers(&self) -> syn::Error {
        syn::Error::new(self.input.last_span(), "expected `triggers`")
    }

    fn error_expected_equals(&self) -> syn::Error {
        syn::Error::new(self.input.last_span(), "expected `=`")
    }

    fn error_expected_tuple(&self) -> syn::Error {
        syn::Error::new(self.input.last_span(), "expected tuple")
    }

    fn error_ambiguous_expression(&self) -> syn::Error {
        syn::Error::new(self.input.last_span(), "found || and && in the same subexpression")
    }
}
