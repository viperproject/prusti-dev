/// The preparser processes Prusti syntax into Rust syntax.
use proc_macro2::{Delimiter, Span, TokenStream, TokenTree};
use proc_macro2::{Punct, Spacing::*};
use quote::{quote, quote_spanned, ToTokens};
use std::collections::VecDeque;
use syn::{
    parse::{Parse, ParseStream},
    spanned::Spanned,
};

/// The representation of an argument to a quantifier (for example `a: i32`)
#[derive(Debug, Clone)]
pub struct Arg {
    pub name: syn::Ident,
    pub typ: syn::Type,
}

pub fn parse_prusti(tokens: TokenStream) -> syn::Result<TokenStream> {
    let parsed = PrustiTokenStream::new(tokens).parse()?;
    // to make sure we catch errors in the Rust syntax early (and with the
    // correct spans), we try to parse the resulting stream using syn here
    syn::parse2::<syn::Expr>(parsed.clone())?;
    Ok(parsed)
}
pub fn parse_prusti_pledge(tokens: TokenStream) -> syn::Result<TokenStream> {
    // TODO: pledges with reference that is not "result" are not supported;
    // for this reason we assert here that the reference (if there is any) is "result"
    // then return the RHS only
    let (reference, rhs) = PrustiTokenStream::new(tokens).parse_pledge()?;
    if let Some(reference) = reference {
        if reference.to_string() != "result" {
            return err(
                reference.span(),
                "reference of after_expiry must be \"result\"",
            );
        }
    }
    syn::parse2::<syn::Expr>(rhs.clone())?;
    Ok(rhs)
}

pub fn parse_prusti_assert_pledge(tokens: TokenStream) -> syn::Result<(TokenStream, TokenStream)> {
    // TODO: pledges with reference that is not "result" are not supported;
    // for this reason we assert here that the reference (if there is any) is "result"
    // then return the RHS only
    let (reference, lhs, rhs) = PrustiTokenStream::new(tokens).parse_assert_pledge()?;
    if let Some(reference) = reference {
        if reference.to_string() != "result" {
            return err(
                reference.span(),
                "reference of assert_on_expiry must be \"result\"",
            );
        }
    }
    syn::parse2::<syn::Expr>(lhs.clone())?;
    syn::parse2::<syn::Expr>(rhs.clone())?;
    Ok((lhs, rhs))
}

pub fn parse_type_cond_spec(tokens: TokenStream) -> syn::Result<TypeCondSpecRefinement> {
    syn::parse2(tokens)
}

/*
Preparsing consists of two stages:

1. In [PrustiTokenStream::new], we map a [TokenStream] to a [PrustiTokenStream]
   by identifying unary and binary operators. We also take care of Rust binary
   operators that have lower precedence than the Prusti ones. Note that at this
   token-based stage, a "binary operator" includes e.g. the semicolon for
   statement sequencing.

2. In [PrustiTokenStream::parse], we perform the actual parsing as well as the
   translation back to Rust syntax. The parser is a Pratt parser with binding
   powers defined in [PrustiBinaryOp::binding_power]. Performing translation to
   Rust syntax in this step allows us to not have to define data types for the
   Prusti AST, as we reuse the Rust AST (i.e. [TokenTree] and [TokenStream]).
*/

/// The preparser reuses [syn::Result] to integrate with the rest of the specs
/// library, even though syn is not used here.
fn error(span: Span, msg: &str) -> syn::Error {
    syn::Error::new(span, msg)
}

/// Same as `error`, conveniently packaged as `syn::Result::Err`.
fn err<T>(span: Span, msg: &str) -> syn::Result<T> {
    Err(error(span, msg))
}

#[derive(Debug, Clone)]
struct PrustiTokenStream {
    tokens: VecDeque<PrustiToken>,
    source_span: Span,
    // TODO: can we somehow update the span after popping stuff?
}

impl PrustiTokenStream {
    /// Constructs a stream of Prusti tokens from a stream of Rust tokens.
    fn new(source: TokenStream) -> Self {
        let source_span = source.span();
        let source = source.into_iter().collect::<Vec<_>>();

        let mut pos = 0;
        let mut tokens = VecDeque::new();

        // TODO: figure out syntax for spec entailments (|= is taken in Rust)

        while pos < source.len() {
            // no matter what tokens we see, we will consume at least one
            pos += 1;
            tokens.push_back(match (&source[pos - 1], source.get(pos), source.get(pos + 1), source.get(pos + 2)) {
                (
                    TokenTree::Punct(p1),
                    Some(TokenTree::Punct(p2)),
                    Some(TokenTree::Punct(p3)),
                    Some(TokenTree::Punct(p4)),
                ) if let Some(op) = PrustiToken::parse_op4(p1, p2, p3, p4) => {
                    // this was a four-character operator, consume three
                    // additional tokens
                    pos += 3;
                    op
                }
                (
                    TokenTree::Punct(p1),
                    Some(TokenTree::Punct(p2)),
                    Some(TokenTree::Punct(p3)),
                    _
                ) if let Some(op) = PrustiToken::parse_op3(p1, p2, p3) => {
                    // this was a three-character operator, consume two
                    // additional tokens
                    pos += 2;
                    op
                }
                (
                    TokenTree::Punct(p1),
                    Some(TokenTree::Punct(p2)),
                    _,
                    _,
                ) if let Some(op) = PrustiToken::parse_op2(p1, p2) => {
                    // this was a two-character operator, consume one
                    // additional token
                    pos += 1;
                    op
                }
                (TokenTree::Ident(ident), _, _, _) if ident == "outer" =>
                    PrustiToken::Outer(ident.span()),
                (TokenTree::Ident(ident), _, _, _) if ident == "forall" =>
                    PrustiToken::Quantifier(ident.span(), Quantifier::Forall),
                (TokenTree::Ident(ident), _, _, _) if ident == "exists" =>
                    PrustiToken::Quantifier(ident.span(), Quantifier::Exists),
                (TokenTree::Punct(punct), _, _, _)
                    if punct.as_char() == ',' && punct.spacing() == Alone =>
                    PrustiToken::BinOp(punct.span(), PrustiBinaryOp::Rust(RustOp::Comma)),
                (TokenTree::Punct(punct), _, _, _)
                    if punct.as_char() == ';' && punct.spacing() == Alone =>
                    PrustiToken::BinOp(punct.span(), PrustiBinaryOp::Rust(RustOp::Semicolon)),
                (TokenTree::Punct(punct), _, _, _)
                    if punct.as_char() == '=' && punct.spacing() == Alone =>
                    PrustiToken::BinOp(punct.span(), PrustiBinaryOp::Rust(RustOp::Assign)),
                (token @ TokenTree::Punct(punct), _, _, _) if punct.spacing() == Joint => {
                    // make sure to fully consume any Rust operator
                    // to avoid later mis-identifying its suffix
                    tokens.push_back(PrustiToken::Token(token.clone()));
                    while let Some(token @ TokenTree::Punct(p)) = source.get(pos) {
                        pos += 1;
                        tokens.push_back(PrustiToken::Token(token.clone()));
                        if p.spacing() != Joint {
                            break;
                        }
                    }
                    continue;
                }
                (TokenTree::Group(group), _, _, _) => PrustiToken::Group(
                    group.span(),
                    group.delimiter(),
                    Box::new(Self::new(group.stream())),
                ),
                (token, _, _, _) => PrustiToken::Token(token.clone()),
            });
        }
        Self {
            tokens,
            source_span,
        }
    }

    fn is_empty(&self) -> bool {
        self.tokens.is_empty()
    }

    fn parse_rest<T, F>(mut self, f: F) -> syn::Result<T>
    where
        F: FnOnce(&mut Self) -> syn::Result<T>,
    {
        let result = f(&mut self)?;
        if !self.is_empty() {
            let start = self.tokens.front().expect("unreachable").span();
            let end = self.tokens.back().expect("unreachable").span();
            let span = join_spans(start, end);
            return err(span, "unexpected extra tokens");
        }
        Ok(result)
    }

    /// Processes a Prusti token stream back into Rust syntax.
    /// Prusti-specific syntax is allowed and translated.
    fn parse(mut self) -> syn::Result<TokenStream> {
        self.expr_bp(0)
    }

    /// Processes a Prusti token stream back into Rust syntax.
    /// Prusti-specific syntax is not allowed and will raise an error.
    fn parse_rust_only(self) -> syn::Result<TokenStream> {
        Ok(TokenStream::from_iter(
            self.tokens
                .into_iter()
                .map(|token| match token {
                    PrustiToken::Group(_, _, box stream) => stream.parse_rust_only(),
                    PrustiToken::Token(tree) => Ok(tree.to_token_stream()),
                    PrustiToken::BinOp(span, PrustiBinaryOp::Rust(op)) => Ok(op.to_tokens(span)),
                    _ => err(token.span(), "unexpected Prusti syntax"),
                })
                .collect::<Result<Vec<_>, _>>()?
                .into_iter(),
        ))
    }

    /// Processes a Prusti token stream for a pledge, in the form `a => b` or
    /// just `b`.
    fn parse_pledge(self) -> syn::Result<(Option<TokenStream>, TokenStream)> {
        let mut pledge_ops = self.split(PrustiBinaryOp::Rust(RustOp::Arrow), false);
        if pledge_ops.len() == 1 {
            Ok((None, pledge_ops[0].expr_bp(0)?))
        } else if pledge_ops.len() == 2 {
            Ok((Some(pledge_ops[0].expr_bp(0)?), pledge_ops[1].expr_bp(0)?))
        } else {
            err(Span::call_site(), "too many arrows in after_expiry")
        }
    }

    /// Processes a Prusti token stream for an assert pledge, in the form `a =>
    /// b, c` or `b, c`.
    fn parse_assert_pledge(self) -> syn::Result<(Option<TokenStream>, TokenStream, TokenStream)> {
        let mut pledge_ops = self.split(PrustiBinaryOp::Rust(RustOp::Arrow), false);
        let (reference, body) = match (pledge_ops.pop(), pledge_ops.pop(), pledge_ops.pop()) {
            (Some(body), None, _) => (None, body),
            (Some(body), Some(mut reference), None) => (Some(reference.expr_bp(0)?), body),
            _ => return err(Span::call_site(), "too many arrows in assert_on_expiry"),
        };
        let mut body_parts = body.split(PrustiBinaryOp::Rust(RustOp::Comma), false);
        if body_parts.len() == 2 {
            Ok((
                reference,
                body_parts[0].expr_bp(0)?,
                body_parts[1].expr_bp(0)?,
            ))
        } else {
            err(Span::call_site(), "missing assertion")
        }
    }

    /// The core of the Pratt parser algorithm. [self.tokens] is the source of
    /// "lexemes". [min_bp] is the minimum binding power we need to see when
    /// identifying a binary operator.
    /// See https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
    fn expr_bp(&mut self, min_bp: u8) -> syn::Result<TokenStream> {
        let mut lhs = match self.tokens.pop_front() {
            Some(PrustiToken::Group(span, delimiter, box stream)) => {
                let mut group = proc_macro2::Group::new(delimiter, stream.parse()?);
                group.set_span(span);
                TokenTree::Group(group).to_token_stream()
            }
            Some(PrustiToken::Outer(span)) => {
                let _stream = self
                    .pop_group(Delimiter::Parenthesis)
                    .ok_or_else(|| error(span, "expected parenthesized expression after outer"))?;
                todo!()
            }
            Some(PrustiToken::Quantifier(span, kind)) => {
                let mut stream = self.pop_group(Delimiter::Parenthesis).ok_or_else(|| {
                    error(span, "expected parenthesized expression after quantifier")
                })?;
                let args = stream
                    .pop_closure_args()
                    .ok_or_else(|| error(span, "expected quantifier body"))?;

                {
                    // for quantifiers, argument types must be explicit
                    // here we parse the closure with syn and check each
                    // argument has a type annotation
                    let cl_args = args.clone().parse_rust_only()?;
                    let check_cl = quote! { | #cl_args | 0 };
                    let parsed_cl = syn::parse2::<syn::ExprClosure>(check_cl)?;
                    for pat in parsed_cl.inputs {
                        match pat {
                            syn::Pat::Type(_) => {}
                            _ => {
                                return err(
                                    pat.span(),
                                    "quantifier arguments must have explicit types",
                                )
                            }
                        }
                    }
                };

                let triggers = stream.extract_triggers()?;
                if args.is_empty() {
                    return err(span, "a quantifier must have at least one argument");
                }
                let args = args.parse()?;
                let body = stream.parse()?;
                kind.translate(span, triggers, args, body)
            }

            Some(PrustiToken::SpecEnt(span, _)) | Some(PrustiToken::CallDesc(span, _)) => {
                return err(span, "unexpected operator")
            }

            // some Rust binary operators can appear on their own, e.g. `(..)`
            Some(PrustiToken::BinOp(span, PrustiBinaryOp::Rust(op))) => op.to_tokens(span),

            Some(PrustiToken::BinOp(span, _)) => return err(span, "unexpected binary operator"),
            Some(PrustiToken::Token(token)) => token.to_token_stream(),
            None => return Ok(TokenStream::new()),
        };
        loop {
            let (span, op) = match self.tokens.front() {
                // If we see a group or token, we simply add them to the
                // current LHS. This way fragments of Rust code with higher-
                // precedence operators (e.g. plus) are connected into atoms
                // as far as our parser is concerned.
                Some(PrustiToken::Group(span, delimiter, box stream)) => {
                    let mut group = proc_macro2::Group::new(*delimiter, stream.clone().parse()?);
                    group.set_span(*span);
                    lhs.extend(TokenTree::Group(group).to_token_stream());
                    self.tokens.pop_front();
                    continue;
                }
                Some(PrustiToken::Token(token)) => {
                    lhs.extend(token.to_token_stream());
                    self.tokens.pop_front();
                    continue;
                }

                Some(PrustiToken::SpecEnt(span, once)) => {
                    let span = *span;
                    let once = *once;
                    self.tokens.pop_front();
                    let args = self
                        .pop_closure_args()
                        .ok_or_else(|| error(span, "expected closure arguments"))?;
                    let nested_closure_specs = self.pop_group_of_nested_specs(span)?;
                    lhs = translate_spec_ent(
                        span,
                        once,
                        lhs,
                        args.split(PrustiBinaryOp::Rust(RustOp::Comma), true)
                            .into_iter()
                            .map(|stream| stream.parse())
                            .collect::<Result<Vec<_>, _>>()?,
                        nested_closure_specs,
                    );
                    continue;
                }

                Some(PrustiToken::CallDesc(..)) => todo!("call desc"),

                Some(PrustiToken::BinOp(span, op)) => (*span, *op),
                Some(PrustiToken::Outer(span)) => return err(*span, "unexpected outer"),
                Some(PrustiToken::Quantifier(span, _)) => {
                    return err(*span, "unexpected quantifier")
                }

                None => break,
            };
            let (l_bp, r_bp) = op.binding_power();
            if l_bp < min_bp {
                break;
            }
            self.tokens.pop_front();
            let rhs = self.expr_bp(r_bp)?;

            // In [new], when identifying consecutive sequences of operators,
            // we delegate to `parse_op*` which identifies Rust operators. In
            // some cases, such as `..`, the binary operator does not actually
            // require a RHS. Thus we only emit this error for operators that
            // Prusti defines, as the actual Rust operators will raise a parse
            // error after desugaring anyway.
            if !matches!(op, PrustiBinaryOp::Rust(_)) && rhs.is_empty() {
                return err(span, "expected expression");
            }
            lhs = op.translate(span, lhs, rhs);
        }
        Ok(lhs)
    }

    fn pop_group(&mut self, delimiter: Delimiter) -> Option<Self> {
        match self.tokens.pop_front() {
            Some(PrustiToken::Group(_, del, box stream)) if del == delimiter => Some(stream),
            _ => None,
        }
    }

    fn pop_closure_args(&mut self) -> Option<Self> {
        let mut tokens = VecDeque::new();

        // special case: empty closure might be parsed as a logical or
        if matches!(
            self.tokens.front(),
            Some(PrustiToken::BinOp(_, PrustiBinaryOp::Or))
        ) {
            return Some(Self {
                tokens,
                source_span: self.source_span,
            });
        }

        if !self.tokens.pop_front()?.is_closure_brace() {
            return None;
        }
        loop {
            let token = self.tokens.pop_front()?;
            if token.is_closure_brace() {
                break;
            }
            tokens.push_back(token);
        }

        Some(Self {
            tokens,
            source_span: self.source_span,
        })
    }

    fn pop_parenthesized_group(&mut self) -> syn::Result<Self> {
        match self.tokens.pop_front() {
            Some(PrustiToken::Group(_span, Delimiter::Parenthesis, box group)) => {
                Ok(group) // TODO: need to clone()?
            }
            _ => Err(error(self.source_span, "expected parenthesized group")),
        }
    }

    fn pop_single_nested_spec(&mut self) -> syn::Result<NestedSpec<Self>> {
        let first = self
            .tokens
            .pop_front()
            .ok_or_else(|| error(self.source_span, "expected nested spec"))?;
        if let PrustiToken::Token(TokenTree::Ident(spec_type)) = first {
            match spec_type.to_string().as_ref() {
                "requires" => Ok(NestedSpec::Requires(self.pop_parenthesized_group()?)),
                "ensures" => Ok(NestedSpec::Ensures(self.pop_parenthesized_group()?)),
                "pure" => Ok(NestedSpec::Pure),
                other => err(
                    self.source_span,
                    format!("unexpected nested spec type: {other}").as_ref(),
                ),
            }
        } else {
            err(self.source_span, "expected identifier")
        }
    }

    fn pop_group_of_nested_specs(
        &mut self,
        span: Span,
    ) -> syn::Result<Vec<NestedSpec<TokenStream>>> {
        let group_of_specs = self
            .pop_group(Delimiter::Bracket)
            .ok_or_else(|| error(span, "expected nested specification in brackets"))?;
        let parsed = group_of_specs
            .split(PrustiBinaryOp::Rust(RustOp::Comma), true)
            .into_iter()
            .map(|stream| stream.parse_rest(|stream| stream.pop_single_nested_spec()))
            .map(|stream| stream.and_then(|s| s.parse()))
            .collect::<syn::Result<Vec<NestedSpec<TokenStream>>>>()?;
        Ok(parsed)
    }

    fn split(self, split_on: PrustiBinaryOp, allow_trailing: bool) -> Vec<Self> {
        if self.tokens.is_empty() {
            return vec![];
        }
        let mut res = self
            .tokens
            .into_iter()
            .collect::<Vec<_>>()
            .split(|token| matches!(token, PrustiToken::BinOp(_, t) if *t == split_on))
            .map(|group| Self {
                tokens: group.iter().cloned().collect(),
                source_span: self.source_span,
            })
            .collect::<Vec<_>>();
        if allow_trailing && res.len() > 1 && res[res.len() - 1].tokens.is_empty() {
            res.pop();
        }
        res
    }

    fn extract_triggers(&mut self) -> syn::Result<Vec<Vec<TokenStream>>> {
        let len = self.tokens.len();
        if len < 4 {
            return Ok(vec![]);
        }
        match [
            &self.tokens[len - 4],
            &self.tokens[len - 3],
            &self.tokens[len - 2],
            &self.tokens[len - 1],
        ] {
            [PrustiToken::BinOp(_, PrustiBinaryOp::Rust(RustOp::Comma)), PrustiToken::Token(TokenTree::Ident(ident)), PrustiToken::BinOp(_, PrustiBinaryOp::Rust(RustOp::Assign)), PrustiToken::Group(triggers_span, Delimiter::Bracket, box triggers)]
                if ident == "triggers" =>
            {
                let triggers = triggers
                    .clone()
                    .split(PrustiBinaryOp::Rust(RustOp::Comma), true)
                    .into_iter()
                    .map(|mut stream| {
                        stream
                            .pop_group(Delimiter::Parenthesis)
                            .ok_or_else(|| {
                                error(*triggers_span, "trigger sets must be tuples of expressions")
                            })?
                            .split(PrustiBinaryOp::Rust(RustOp::Comma), true)
                            .into_iter()
                            .map(|stream| stream.parse())
                            .collect::<Result<Vec<_>, _>>()
                    })
                    .collect::<Result<Vec<_>, _>>();
                self.tokens.truncate(len - 4);
                triggers
            }
            _ => Ok(vec![]),
        }
    }
}

#[derive(Debug)]
pub struct TypeCondSpecRefinement {
    pub trait_bounds: Vec<syn::PredicateType>,
    pub specs: Vec<NestedSpec<TokenStream>>,
}

impl Parse for TypeCondSpecRefinement {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        input
            .parse::<syn::Token![where]>()
            .map_err(with_type_cond_spec_example)?;
        Ok(TypeCondSpecRefinement {
            trait_bounds: parse_trait_bounds(input)?,
            specs: PrustiTokenStream::new(input.parse().unwrap())
                .parse_rest(|pts| pts.pop_group_of_nested_specs(input.span()))?,
        })
    }
}

fn parse_trait_bounds(input: ParseStream) -> syn::Result<Vec<syn::PredicateType>> {
    let mut bounds: Vec<syn::PredicateType> = Vec::new();
    loop {
        let predicate = input
            .parse::<syn::WherePredicate>()
            .map_err(with_type_cond_spec_example)?;
        bounds.push(validate_predicate(predicate)?);
        input
            .parse::<syn::token::Comma>()
            .map_err(with_type_cond_spec_example)?;
        if input.peek(syn::token::Bracket) || input.is_empty() {
            // now expecting specs in []
            // also breaking when empty, to handle that as missing specs rather than a missing constraint
            break;
        }
    }
    Ok(bounds)
}

fn validate_predicate(predicate: syn::WherePredicate) -> syn::Result<syn::PredicateType> {
    use syn::WherePredicate::*;

    match predicate {
        Type(type_bound) => {
            validate_trait_bounds(&type_bound)?;
            Ok(type_bound)
        }
        Lifetime(lifetime_bound) => disallowed_lifetime_error(lifetime_bound.span()),
        Eq(eq_bound) => err(
            eq_bound.span(),
            "equality constraints are not allowed in type-conditional spec refinements",
        ),
    }
}

fn disallowed_lifetime_error<T>(span: Span) -> syn::Result<T> {
    err(
        span,
        "lifetimes are not allowed in type-conditional spec refinement trait bounds",
    )
}

fn validate_trait_bounds(trait_bounds: &syn::PredicateType) -> syn::Result<()> {
    if let Some(lifetimes) = &trait_bounds.lifetimes {
        return disallowed_lifetime_error(lifetimes.span());
    }
    for bound in &trait_bounds.bounds {
        match bound {
            syn::TypeParamBound::Lifetime(lt) => {
                return disallowed_lifetime_error(lt.span());
            }
            syn::TypeParamBound::Trait(trait_bound) => {
                if let Some(lt) = &trait_bound.lifetimes {
                    return disallowed_lifetime_error(lt.span());
                }
            }
        }
    }

    Ok(())
}

fn with_type_cond_spec_example(mut err: syn::Error) -> syn::Error {
    err.combine(error(err.span(), "expected where constraint and specifications in brackets, e.g.: `refine_spec(where T: A + B, U: C, [requires(...), ...])`"));
    err
}

/// A specification enclosed in another specification (e.g. in spec entailments or type-conditional spec refinements)
#[derive(Debug)]
pub enum NestedSpec<T> {
    Requires(T),
    Ensures(T),
    Pure,
}

impl NestedSpec<PrustiTokenStream> {
    fn parse(self) -> syn::Result<NestedSpec<TokenStream>> {
        Ok(match self {
            NestedSpec::Requires(stream) => NestedSpec::Requires(stream.parse()?),
            NestedSpec::Ensures(stream) => NestedSpec::Ensures(stream.parse()?),
            NestedSpec::Pure => NestedSpec::Pure,
        })
    }
}

#[derive(Debug, Clone)]
enum PrustiToken {
    Group(Span, Delimiter, Box<PrustiTokenStream>),
    Token(TokenTree),
    BinOp(Span, PrustiBinaryOp),
    // TODO: add note about unops not sharing a variant, descriptions ...
    Outer(Span),
    Quantifier(Span, Quantifier),
    SpecEnt(Span, bool),
    CallDesc(Span, bool),
}

fn translate_spec_ent(
    span: Span,
    once: bool,
    cl_expr: TokenStream,
    cl_args: Vec<TokenStream>,
    contract: Vec<NestedSpec<TokenStream>>,
) -> TokenStream {
    let once = if once {
        quote_spanned! { span => true }
    } else {
        quote_spanned! { span => false }
    };

    // TODO: move extraction function generation into "fn_type_extractor"
    let arg_count = cl_args.len();
    let generics_args = (0..arg_count)
        .map(|i| TokenTree::Ident(proc_macro2::Ident::new(&format!("GA{i}"), span)))
        .collect::<Vec<_>>();
    let generic_res = TokenTree::Ident(proc_macro2::Ident::new("GR", span));

    let extract_args = (0..arg_count)
        .map(|i| TokenTree::Ident(proc_macro2::Ident::new(&format!("__extract_arg{i}"), span)))
        .collect::<Vec<_>>();
    let extract_args_decl = extract_args
        .iter()
        .zip(generics_args.iter())
        .map(|(ident, arg_type)| {
            quote_spanned! { span =>
                #[prusti::spec_only]
                fn #ident<
                    #(#generics_args),* ,
                    #generic_res,
                    F: FnOnce( #(#generics_args),* ) -> #generic_res
                >(_f: &F) -> #arg_type { unreachable!() }
            }
        })
        .collect::<Vec<_>>();

    let preconds = contract
        .iter()
        .filter_map(|spec| match spec {
            NestedSpec::Requires(stream) => Some(stream.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let postconds = contract
        .into_iter()
        .filter_map(|spec| match spec {
            NestedSpec::Ensures(stream) => Some(stream),
            _ => None,
        })
        .collect::<Vec<_>>();

    // TODO: figure out `outer`

    quote_spanned! { span => {
        let __cl_ref = & #cl_expr;
        #(#extract_args_decl)*
        #[prusti::spec_only]
        fn __extract_res<
            #(#generics_args),* ,
            #generic_res,
            F: FnOnce( #(#generics_args),* ) -> #generic_res
        >(_f: &F) -> #generic_res { unreachable!() }
        #( let #cl_args = #extract_args(__cl_ref); )*
        let result = __extract_res(__cl_ref);
        specification_entailment(
            #once,
            __cl_ref,
            ( #( #[prusti::spec_only] || -> bool { ((#preconds): bool) }, )* ),
            ( #( #[prusti::spec_only] || -> bool { ((#postconds): bool) }, )* ),
        )
    } }
}

#[derive(Debug, Clone)]
enum Quantifier {
    Forall,
    Exists,
}

impl Quantifier {
    fn translate(
        &self,
        span: Span,
        triggers: Vec<Vec<TokenStream>>,
        args: TokenStream,
        body: TokenStream,
    ) -> TokenStream {
        let full_span = join_spans(span, body.span());
        let trigger_sets = triggers
            .into_iter()
            .map(|set| {
                let triggers = TokenStream::from_iter(set.into_iter().map(|trigger| {
                    quote_spanned! { trigger.span() =>
                    #[prusti::spec_only] | #args | ( #trigger ), }
                }));
                quote_spanned! { full_span => ( #triggers ) }
            })
            .collect::<Vec<_>>();
        let body = quote_spanned! { body.span() => ((#body): bool) };
        match self {
            Self::Forall => quote_spanned! { full_span => ::prusti_contracts::forall(
                ( #( #trigger_sets, )* ),
                #[prusti::spec_only] | #args | -> bool { #body }
            ) },
            Self::Exists => quote_spanned! { full_span => ::prusti_contracts::exists(
                ( #( #trigger_sets, )* ),
                #[prusti::spec_only] | #args | -> bool { #body }
            ) },
        }
    }
}

// For Prusti-specific operators, in [operator2], [operator3], and [operator4]
// we mainly care about the spacing of the last [Punct], as this lets us
// know that the last character is not itself part of an actual Rust
// operator.
//
// "==>" should still have the expected spacing of [Joint, Joint, Alone]
// even though "==" and ">" are separate Rust operators.
fn operator2(op: &str, p1: &Punct, p2: &Punct) -> bool {
    let chars = op.chars().collect::<Vec<_>>();
    [p1.as_char(), p2.as_char()] == chars[0..2] && p1.spacing() == Joint && p2.spacing() == Alone
}

fn operator3(op: &str, p1: &Punct, p2: &Punct, p3: &Punct) -> bool {
    let chars = op.chars().collect::<Vec<_>>();
    [p1.as_char(), p2.as_char(), p3.as_char()] == chars[0..3]
        && p1.spacing() == Joint
        && p2.spacing() == Joint
        && p3.spacing() == Alone
}

fn operator4(op: &str, p1: &Punct, p2: &Punct, p3: &Punct, p4: &Punct) -> bool {
    let chars = op.chars().collect::<Vec<_>>();
    [p1.as_char(), p2.as_char(), p3.as_char(), p4.as_char()] == chars[0..4]
        && p1.spacing() == Joint
        && p2.spacing() == Joint
        && p3.spacing() == Joint
        && p4.spacing() == Alone
}

impl PrustiToken {
    fn span(&self) -> Span {
        match self {
            Self::Group(span, _, _)
            | Self::BinOp(span, _)
            | Self::Outer(span)
            | Self::Quantifier(span, _)
            | Self::SpecEnt(span, _)
            | Self::CallDesc(span, _) => *span,
            Self::Token(tree) => tree.span(),
        }
    }

    fn is_closure_brace(&self) -> bool {
        matches!(self, Self::Token(TokenTree::Punct(p))
            if p.as_char() == '|' && p.spacing() == proc_macro2::Spacing::Alone)
    }

    fn parse_op2(p1: &Punct, p2: &Punct) -> Option<Self> {
        let span = join_spans(p1.span(), p2.span());
        Some(Self::BinOp(
            span,
            if operator2("&&", p1, p2) {
                PrustiBinaryOp::And
            } else if operator2("||", p1, p2) {
                PrustiBinaryOp::Or
            } else if operator2("->", p1, p2) {
                PrustiBinaryOp::Implies
            } else if operator2("..", p1, p2) {
                PrustiBinaryOp::Rust(RustOp::Range)
            } else if operator2("+=", p1, p2) {
                PrustiBinaryOp::Rust(RustOp::AddAssign)
            } else if operator2("-=", p1, p2) {
                PrustiBinaryOp::Rust(RustOp::SubtractAssign)
            } else if operator2("*=", p1, p2) {
                PrustiBinaryOp::Rust(RustOp::MultiplyAssign)
            } else if operator2("/=", p1, p2) {
                PrustiBinaryOp::Rust(RustOp::DivideAssign)
            } else if operator2("%=", p1, p2) {
                PrustiBinaryOp::Rust(RustOp::ModuloAssign)
            } else if operator2("&=", p1, p2) {
                PrustiBinaryOp::Rust(RustOp::BitAndAssign)
            //} else if operator2("|=", p1, p2) {
            //    PrustiBinaryOp::Rust(RustOp::BitOrAssign)
            } else if operator2("^=", p1, p2) {
                PrustiBinaryOp::Rust(RustOp::BitXorAssign)
            } else if operator2("=>", p1, p2) {
                PrustiBinaryOp::Rust(RustOp::Arrow)
            } else if operator2("|=", p1, p2) {
                return Some(Self::SpecEnt(span, false));
            } else if operator2("~>", p1, p2) {
                return Some(Self::CallDesc(span, false));
            } else {
                return None;
            },
        ))
    }

    fn parse_op3(p1: &Punct, p2: &Punct, p3: &Punct) -> Option<Self> {
        let span = join_spans(join_spans(p1.span(), p2.span()), p3.span());
        Some(Self::BinOp(
            span,
            if operator3("==>", p1, p2, p3) {
                PrustiBinaryOp::Implies
            } else if operator3("<==", p1, p2, p3) {
                PrustiBinaryOp::ImpliesReverse
            } else if operator3("===", p1, p2, p3) {
                PrustiBinaryOp::SnapEq
            } else if operator3("!==", p1, p2, p3) {
                PrustiBinaryOp::SnapNe
            } else if operator3("..=", p1, p2, p3) {
                PrustiBinaryOp::Rust(RustOp::RangeInclusive)
            } else if operator3("<<=", p1, p2, p3) {
                PrustiBinaryOp::Rust(RustOp::LeftShiftAssign)
            } else if operator3(">>=", p1, p2, p3) {
                PrustiBinaryOp::Rust(RustOp::RightShiftAssign)
            } else if operator3("|=!", p1, p2, p3) {
                return Some(Self::SpecEnt(span, true));
            } else if operator3("~>!", p1, p2, p3) {
                return Some(Self::CallDesc(span, true));
            } else {
                return None;
            },
        ))
    }

    fn parse_op4(p1: &Punct, p2: &Punct, p3: &Punct, p4: &Punct) -> Option<Self> {
        let span = join_spans(
            join_spans(join_spans(p1.span(), p2.span()), p3.span()),
            p4.span(),
        );
        Some(Self::BinOp(
            span,
            if operator4("<==>", p1, p2, p3, p4) {
                PrustiBinaryOp::Iff
            } else {
                return None;
            },
        ))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PrustiBinaryOp {
    Rust(RustOp),
    Iff,
    Implies,
    ImpliesReverse,
    Or,
    And,
    SnapEq,
    SnapNe,
}

impl PrustiBinaryOp {
    /// This function defines both the precedence and associativity of each
    /// binary operator. The result is used in [PrustiTokenStream::expr_bp].
    /// The value is the "power" with which each side of the binary operator
    /// binds to its LHS resp. RHS. So, given:
    ///
    /// binop1  expr  binop2
    ///
    /// Where binop1 has binding power (_, 3) and binop2 (4, _), then binop2
    /// will bind to expr first, as 4 > 3.
    ///
    /// Associativity is likewise defined by making sure that each side of the
    /// binding power is different. (4, 3) is right associative, (3, 4) is left
    /// associative.
    fn binding_power(&self) -> (u8, u8) {
        // TODO: should <== and ==> have the same binding power? === and !==?
        match self {
            Self::Rust(_) => (0, 0),
            Self::Iff => (4, 3),
            Self::Implies => (6, 5),
            Self::ImpliesReverse => (5, 6),
            Self::Or => (7, 8),
            Self::And => (9, 10),
            Self::SnapEq => (11, 12),
            Self::SnapNe => (11, 12),
        }
    }

    fn translate(&self, span: Span, raw_lhs: TokenStream, raw_rhs: TokenStream) -> TokenStream {
        // TODO: enforce types more strictly with type ascriptions
        let lhs = quote_spanned! { raw_lhs.span() => (#raw_lhs) };
        let rhs = quote_spanned! { raw_rhs.span() => (#raw_rhs) };
        match self {
            Self::Rust(op) => op.translate(span, raw_lhs, raw_rhs),
            Self::Iff => {
                let joined_span = join_spans(lhs.span(), rhs.span());
                quote_spanned! { joined_span => #lhs == #rhs }
            }
            // implication is desugared into this form to avoid evaluation
            // order issues: `f(a, b)` makes Rust evaluate both `a` and `b`
            // before the `f` call
            Self::Implies => {
                let joined_span = join_spans(lhs.span(), rhs.span());
                // preserve span of LHS
                let not_lhs = quote_spanned! { lhs.span() => !#lhs };
                quote_spanned! { joined_span => #not_lhs || #rhs }
            }
            Self::ImpliesReverse => {
                let joined_span = join_spans(lhs.span(), rhs.span());
                // preserve span of RHS
                let not_rhs = quote_spanned! { rhs.span() => !#rhs };
                quote_spanned! { joined_span => #not_rhs || #lhs }
            }
            Self::Or => quote_spanned! { span => #lhs || #rhs },
            Self::And => quote_spanned! { span => #lhs && #rhs },
            Self::SnapEq => {
                let joined_span = join_spans(lhs.span(), rhs.span());
                quote_spanned! { joined_span => snapshot_equality(&#lhs, &#rhs) }
            }
            Self::SnapNe => {
                let joined_span = join_spans(lhs.span(), rhs.span());
                quote_spanned! { joined_span => !snapshot_equality(&#lhs, &#rhs) }
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RustOp {
    RangeInclusive,
    LeftShiftAssign,
    RightShiftAssign,
    Range,
    AddAssign,
    SubtractAssign,
    MultiplyAssign,
    DivideAssign,
    ModuloAssign,
    BitAndAssign,
    // FIXME: |= spec entailment
    // BitOrAssign,
    BitXorAssign,
    Arrow,
    Comma,
    Semicolon,
    Assign,
}

impl RustOp {
    fn translate(&self, span: Span, lhs: TokenStream, rhs: TokenStream) -> TokenStream {
        let op = self.to_tokens(span);
        quote! { #lhs #op #rhs }
    }

    fn to_tokens(self, span: Span) -> TokenStream {
        match self {
            Self::RangeInclusive => quote_spanned! { span => ..= },
            Self::LeftShiftAssign => quote_spanned! { span => <<= },
            Self::RightShiftAssign => quote_spanned! { span => >>= },
            Self::Range => quote_spanned! { span => .. },
            Self::AddAssign => quote_spanned! { span => += },
            Self::SubtractAssign => quote_spanned! { span => -= },
            Self::MultiplyAssign => quote_spanned! { span => *= },
            Self::DivideAssign => quote_spanned! { span => /= },
            Self::ModuloAssign => quote_spanned! { span => %= },
            Self::BitAndAssign => quote_spanned! { span => &= },
            // Self::BitOrAssign => quote_spanned! { span => |= },
            Self::BitXorAssign => quote_spanned! { span => ^= },
            Self::Arrow => quote_spanned! { span => => },
            Self::Comma => quote_spanned! { span => , },
            Self::Semicolon => quote_spanned! { span => ; },
            Self::Assign => quote_spanned! { span => = },
        }
    }
}

fn join_spans(s1: Span, s2: Span) -> Span {
    // Tests don't run in the proc macro context, so this gets a little funky for them
    if cfg!(test) {
        // During tests we don't care so much about returning a default
        s1.join(s2).unwrap_or(s1)
    } else {
        // This works even when compiled with stable, unlike `s1.join(s2)`
        s1.unwrap()
            .join(s2.unwrap())
            .expect("Failed to join spans!")
            .into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! assert_error {
        ( $result:expr, $expected:expr ) => {{
            let _res = $result;
            assert!(_res.is_err());
            let _err = _res.unwrap_err();
            assert_eq!(_err.to_string(), $expected);
        }};
    }

    #[test]
    fn test_preparser() {
        assert_eq!(
            parse_prusti("a ==> b".parse().unwrap())
                .unwrap()
                .to_string(),
            "! (a) || (b)",
        );
        assert_eq!(
            parse_prusti("a === b + c".parse().unwrap())
                .unwrap()
                .to_string(),
            "snapshot_equality (& (a) , & (b + c))",
        );
        assert_eq!(
            parse_prusti("a !== b + c".parse().unwrap())
                .unwrap()
                .to_string(),
            "! snapshot_equality (& (a) , & (b + c))",
        );
        assert_eq!(
            parse_prusti("a ==> b ==> c".parse().unwrap())
                .unwrap()
                .to_string(),
            "! (a) || (! (b) || (c))",
        );
        assert_eq!(
            parse_prusti("(a ==> b && c) ==> d || e".parse().unwrap())
                .unwrap()
                .to_string(),
            "! ((! (a) || ((b) && (c)))) || ((d) || (e))",
        );
        assert_eq!(
            parse_prusti("forall(|x: i32| a ==> b)".parse().unwrap())
                .unwrap()
                .to_string(),
            ":: prusti_contracts :: forall (() , # [prusti :: spec_only] | x : i32 | -> bool { ((! (a) || (b)) : bool) })",
        );
        assert_eq!(
            parse_prusti("exists(|x: i32| a === b)".parse().unwrap()).unwrap().to_string(),
            ":: prusti_contracts :: exists (() , # [prusti :: spec_only] | x : i32 | -> bool { ((snapshot_equality (& (a) , & (b))) : bool) })",
        );
        assert_eq!(
            parse_prusti("forall(|x: i32| a ==> b, triggers = [(c,), (d, e)])".parse().unwrap()).unwrap().to_string(),
            ":: prusti_contracts :: forall (((# [prusti :: spec_only] | x : i32 | (c) ,) , (# [prusti :: spec_only] | x : i32 | (d) , # [prusti :: spec_only] | x : i32 | (e) ,) ,) , # [prusti :: spec_only] | x : i32 | -> bool { ((! (a) || (b)) : bool) })",
        );
        assert_eq!(
            parse_prusti("assert!(a === b ==> b)".parse().unwrap())
                .unwrap()
                .to_string(),
            "assert ! (! (snapshot_equality (& (a) , & (b))) || (b))",
        );
    }

    mod type_cond_specs {
        use std::assert_matches::assert_matches;

        use super::*;

        #[test]
        fn invalid_args() {
            let err_invalid_bounds = "expected one of: `for`, parentheses, `fn`, `unsafe`, `extern`, identifier, `::`, `<`, square brackets, `*`, `&`, `!`, `impl`, `_`, lifetime";
            assert_error!(
                parse_type_cond_spec(quote! { [requires(false)] }),
                "expected `where`"
            );
            assert_error!(
                parse_type_cond_spec(quote! { where [requires(false)] }),
                err_invalid_bounds
            );
            assert_error!(
                parse_type_cond_spec(quote! { [requires(false)], T: A }),
                "expected `where`"
            );
            assert_error!(
                parse_type_cond_spec(quote! { where [requires(false)], T: A }),
                err_invalid_bounds
            );
            assert_error!(
                parse_type_cond_spec(quote! {}),
                format!("unexpected end of input, {}", "expected `where`")
            );
            assert_error!(parse_type_cond_spec(quote! { T: A }), "expected `where`");
            assert_error!(parse_type_cond_spec(quote! { where T: A }), "expected `,`");
            assert_error!(
                parse_type_cond_spec(quote! { where T: A,  }),
                "expected nested specification in brackets"
            );
            assert_error!(
                parse_type_cond_spec(quote! { where T: A, {} }),
                err_invalid_bounds
            );
            assert_error!(
                parse_type_cond_spec(quote! { where T: A [requires(false)] }),
                "expected `,`"
            );
            assert_error!(
                parse_type_cond_spec(quote! { where T: A, [requires(false)], "nope" }),
                "unexpected extra tokens"
            );
        }

        #[test]
        fn multiple_bounds_multiple_specs() {
            let constraint = parse_type_cond_spec(
                quote! { where T: A+B+Foo<i32>, U: C, [requires(true), ensures(false), pure]},
            )
            .unwrap();

            assert_bounds_eq(
                &constraint.trait_bounds,
                &[quote! { T : A + B + Foo < i32 > }, quote! { U : C }],
            );
            match &constraint.specs[0] {
                NestedSpec::Requires(ts) => assert_eq!(ts.to_string(), "true"),
                _ => panic!(),
            }
            match &constraint.specs[1] {
                NestedSpec::Ensures(ts) => assert_eq!(ts.to_string(), "false"),
                _ => panic!(),
            }
            assert_matches!(&constraint.specs[2], NestedSpec::Pure);
            assert_eq!(constraint.specs.len(), 3);
        }

        #[test]
        fn no_specs() {
            let constraint = parse_type_cond_spec(quote! { where T: A, []}).unwrap();
            assert_bounds_eq(&constraint.trait_bounds, &[quote! { T : A }]);
            assert!(constraint.specs.is_empty());
        }

        #[test]
        fn fully_qualified_trait_path() {
            let constraint =
                parse_type_cond_spec(quote! { where T: path::to::A, [requires(true)]}).unwrap();
            assert_bounds_eq(&constraint.trait_bounds, &[quote! { T : path :: to :: A }]);
        }

        #[test]
        fn tuple_generics() {
            // just check that parsing succeeds
            assert!(parse_type_cond_spec(quote! { where T: Fn<(i32,), Output = i32>, []}).is_ok());
            assert!(parse_type_cond_spec(quote! { where T: Fn<(i32,)>, []}).is_ok());
            assert!(parse_type_cond_spec(quote! { where T: Fn<(i32, bool)>, []}).is_ok());
            assert!(parse_type_cond_spec(quote! { where T: Fn<(i32, bool,)>, []}).is_ok());
        }

        fn assert_bounds_eq(parsed: &[syn::PredicateType], quotes: &[TokenStream]) {
            assert_eq!(parsed.len(), quotes.len());
            for (parsed, quote) in parsed.iter().zip(quotes.iter()) {
                assert_eq!(
                    syn::WherePredicate::Type(parsed.clone()),
                    syn::parse_quote! { #quote }
                );
            }
        }
    }
}
