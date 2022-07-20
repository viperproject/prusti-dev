/// The preparser processes Prusti syntax into Rust syntax.

use proc_macro2::{Span, TokenStream, TokenTree, Delimiter, Spacing};
use std::collections::VecDeque;
use quote::{ToTokens, quote, quote_spanned, TokenStreamExt};
use proc_macro2::Punct;
use proc_macro2::Spacing::*;
use syn::spanned::Spanned;

/// The representation of an argument to a quantifier (for example `a: i32`)
#[derive(Debug, Clone)]
pub struct Arg {
    pub name: syn::Ident,
    pub typ: syn::Type
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
            return error(reference.span(), "reference of after_expiry must be \"result\"");
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
            return error(reference.span(), "reference of assert_on_expiry must be \"result\"");
        }
    }
    syn::parse2::<syn::Expr>(lhs.clone())?;
    syn::parse2::<syn::Expr>(rhs.clone())?;
    Ok((lhs, rhs))
}

pub fn parse_ghost_constraint(tokens: TokenStream) -> syn::Result<(TokenStream, Vec<NestedSpec<TokenStream>>)> {
    let pts = PrustiTokenStream::new(tokens);
    pts.parse_ghost_constraint()
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
fn error<T>(span: Span, msg: &str) -> syn::Result<T> {
    syn::Result::Err(syn::parse::Error::new(span, msg))
}

#[derive(Debug, Clone)]
struct PrustiTokenStream {
    tokens: VecDeque<PrustiToken>,
    source_span: Span,
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
            tokens.push_back(match (&source[pos - 1], source.get(pos), source.get(pos + 1)) {
                (
                    TokenTree::Punct(p1),
                    Some(TokenTree::Punct(p2)),
                    Some(TokenTree::Punct(p3)),
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
                ) if let Some(op) = PrustiToken::parse_op2(p1, p2) => {
                    // this was a two-character operator, consume one
                    // additional token
                    pos += 1;
                    op
                }
                (TokenTree::Ident(ident), _, _) if ident == "outer" =>
                    PrustiToken::Outer(ident.span()),
                (TokenTree::Ident(ident), _, _) if ident == "forall" =>
                    PrustiToken::Quantifier(ident.span(), Quantifier::Forall),
                (TokenTree::Ident(ident), _, _) if ident == "exists" =>
                    PrustiToken::Quantifier(ident.span(), Quantifier::Exists),
                (TokenTree::Punct(punct), _, _)
                    if punct.as_char() == ',' && punct.spacing() == Alone =>
                    PrustiToken::BinOp(punct.span(), PrustiBinaryOp::Rust(RustOp::Comma)),
                (TokenTree::Punct(punct), _, _)
                    if punct.as_char() == ';' && punct.spacing() == Alone =>
                    PrustiToken::BinOp(punct.span(), PrustiBinaryOp::Rust(RustOp::Semicolon)),
                (TokenTree::Punct(punct), _, _)
                    if punct.as_char() == '=' && punct.spacing() == Alone =>
                    PrustiToken::BinOp(punct.span(), PrustiBinaryOp::Rust(RustOp::Assign)),
                (token @ TokenTree::Punct(punct), _, _) if punct.spacing() == Joint => {
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
                (TokenTree::Group(group), _, _) => PrustiToken::Group(
                    group.span(),
                    group.delimiter(),
                    box Self::new(group.stream()),
                ),
                (token, _, _) => PrustiToken::Token(token.clone()),
            });
        }
        Self { tokens, source_span }
    }

    fn is_empty(&self) -> bool {
        self.tokens.is_empty()
    }

    /// Processes a Prusti token stream back into Rust syntax.
    /// Prusti-specific syntax is allowed and translated.
    fn parse(mut self) -> syn::Result<TokenStream> {
        self.expr_bp(0)
    }

    /// Processes a Prusti token stream back into Rust syntax.
    /// Prusti-specific syntax is not allowed and will raise an error.
    fn parse_rust_only(self) -> syn::Result<TokenStream> {
        Ok(TokenStream::from_iter(self.tokens
            .into_iter()
            .map(|token| match token {
                PrustiToken::Group(_, _, box stream) => stream.parse_rust_only(),
                PrustiToken::Token(tree) => Ok(tree.to_token_stream()),
                PrustiToken::BinOp(span, PrustiBinaryOp::Rust(op)) => Ok(op.to_tokens(span)),
                _ => error(token.span(), "unexpected Prusti syntax"),
            })
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()))
    }

    /// Processes a Prusti token stream for a pledge, in the form `a => b` or
    /// just `b`.
    fn parse_pledge(self) -> syn::Result<(
        Option<TokenStream>,
        TokenStream
    )> {
        let mut pledge_ops = self.split(PrustiBinaryOp::Rust(RustOp::Arrow), false);
        if pledge_ops.len() == 1 {
            Ok((None, pledge_ops[0].expr_bp(0)?))
        } else if pledge_ops.len() == 2 {
            Ok((Some(pledge_ops[0].expr_bp(0)?), pledge_ops[1].expr_bp(0)?))
        } else {
            error(Span::call_site(), "too many arrows in after_expiry")
        }
    }

    /// Processes a Prusti token stream for an assert pledge, in the form `a =>
    /// b, c` or `b, c`.
    fn parse_assert_pledge(self) -> syn::Result<(
        Option<TokenStream>,
        TokenStream,
        TokenStream
    )> {
        let mut pledge_ops = self.split(PrustiBinaryOp::Rust(RustOp::Arrow), false);
        let (reference, body) = if pledge_ops.len() == 1 {
            (None, pledge_ops.pop().unwrap())
        } else if pledge_ops.len() == 2 {
            (Some(pledge_ops[0].expr_bp(0)?), pledge_ops.pop().unwrap())
        } else {
            return error(Span::call_site(), "too many arrows in assert_on_expiry");
        };
        let mut body_parts = body.split(PrustiBinaryOp::Rust(RustOp::Comma), false);
        if body_parts.len() == 2 {
            Ok((reference, body_parts[0].expr_bp(0)?, body_parts[1].expr_bp(0)?))
        } else {
            error(Span::call_site(), "missing assertion")
        }
    }

    fn parse_ghost_constraint(self) -> syn::Result<(TokenStream, Vec<NestedSpec<TokenStream>>)> {
        let span = self.source_span;
        let mut arguments = self.split(PrustiBinaryOp::Rust(RustOp::Comma), false);
        let parsing_error = || {
            error(span, "Invalid use of macro. Two arguments expected (a trait bound `T: A + B` and multiple specifications `[requires(...), ensures(...), ...]`)")
        };

        if arguments.len() < 2 {
            return parsing_error();
        }

        // We interpret the last element of the arguments as the nested specs and everything before
        // as the ghost constraints.
        // This is due to the fact that the prusti token stream also splits on commas
        // inside the ghost constraint.
        let nested_specs = arguments
            .remove(arguments.len() - 1)
            .pop_group_of_nested_specs(Span::call_site())?;

        let constraint_tokens = arguments.into_iter()
            .map(|arg| arg.parse_rust_only())
            .collect::<Result<Vec<TokenStream>, _>>()?;

        let mut trait_bounds_ts = TokenStream::new();
        trait_bounds_ts.append_separated(constraint_tokens, TokenTree::Punct(Punct::new(',', Spacing::Alone)));

        // let trait_bounds_ts = trait_bounds_ts.parse_rust_only()?;
        Ok((trait_bounds_ts, nested_specs))
    }

    /// The core of the Pratt parser algorithm. [self.tokens] is the source of
    /// "lexemes". [min_bp] is the minimum binding power we need to see when
    /// identifying a binary operator.
    /// See https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
    fn expr_bp(&mut self, min_bp: u8) -> syn::Result<TokenStream> {
        let mut lhs = match self.tokens.pop_front() {
            Some(PrustiToken::Group(span, delimiter, box stream)) => {
                let mut group = proc_macro2::Group::new(
                    delimiter,
                    stream.parse()?,
                );
                group.set_span(span);
                TokenTree::Group(group).to_token_stream()
            }
            Some(PrustiToken::Outer(span)) => {
                let _stream = self.pop_group(Delimiter::Parenthesis)
                    .ok_or_else(|| syn::parse::Error::new(span, "expected parenthesized expression after outer"))?;
                todo!()
            }
            Some(PrustiToken::Quantifier(span, kind)) => {
                let mut stream = self.pop_group(Delimiter::Parenthesis)
                    .ok_or_else(|| syn::parse::Error::new(span, "expected parenthesized expression after quantifier"))?;
                let args = stream.pop_closure_args()
                    .ok_or_else(|| syn::parse::Error::new(span, "expected quantifier body"))?;

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
                            _ => return error(pat.span(), "quantifier arguments must have explicit types"),
                        }
                    }
                };

                let triggers = stream.extract_triggers()?;
                if args.is_empty() {
                    return error(span, "a quantifier must have at least one argument");
                }
                let args = args.parse()?;
                let body = stream.parse()?;
                kind.translate(span, triggers, args, body)
            }

            Some(PrustiToken::SpecEnt(span, _))
            | Some(PrustiToken::CallDesc(span, _)) =>
                return error(span, "unexpected operator"),

            // some Rust binary operators can appear on their own, e.g. `(..)`
            Some(PrustiToken::BinOp(span, PrustiBinaryOp::Rust(op))) =>
                op.to_tokens(span),

            Some(PrustiToken::BinOp(span, _)) =>
                return error(span, "unexpected binary operator"),
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
                    let mut group = proc_macro2::Group::new(
                        *delimiter,
                        stream.clone().parse()?,
                    );
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
                    let args = self.pop_closure_args()
                        .ok_or_else(|| syn::parse::Error::new(span, "expected closure arguments"))?;
                    let nested_closure_specs = self.pop_group_of_nested_specs(span)?;
                    lhs = translate_spec_ent(
                        span,
                        once,
                        lhs,
                        args
                            .split(PrustiBinaryOp::Rust(RustOp::Comma), true)
                            .into_iter()
                            .map(|stream| stream.parse())
                            .collect::<Result<Vec<_>, _>>()?,
                        nested_closure_specs,
                    );
                    continue;
                }

                Some(PrustiToken::CallDesc(..)) => todo!("call desc"),

                Some(PrustiToken::BinOp(span, op)) => (*span, *op),
                Some(PrustiToken::Outer(span)) =>
                    return error(*span, "unexpected outer"),
                Some(PrustiToken::Quantifier(span, _)) =>
                    return error(*span, "unexpected quantifier"),

                None => break,
            };
            let (l_bp, r_bp) = op.binding_power();
            if l_bp < min_bp {
                break;
            }
            self.tokens.pop_front();
            let rhs = self.expr_bp(r_bp)?;
            // TODO: explain
            if !matches!(op, PrustiBinaryOp::Rust(_)) && rhs.is_empty() {
                return error(span, "expected expression");
            }
            lhs = op.translate(span, lhs, rhs);
        }
        Ok(lhs)
    }

    fn pop_group(&mut self, delimiter: Delimiter) -> Option<Self> {
        match self.tokens.pop_front() {
            Some(PrustiToken::Group(_, del, box stream)) if del == delimiter
                => Some(stream),
            _ => None,
        }
    }

    fn pop_closure_args(&mut self) -> Option<Self> {
        let mut tokens = VecDeque::new();

        // special case: empty closure might be parsed as a logical or
        if matches!(self.tokens.front(), Some(PrustiToken::BinOp(_, PrustiBinaryOp::Or))) {
            return Some(Self { tokens, source_span: self.source_span });
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

        Some(Self { tokens, source_span: self.source_span })
    }

    fn pop_one_nested_spec(self) -> Option<NestedSpec<Self>> {
        // TODO: clean up the interface somehow ...
        if self.tokens.is_empty() {
            return None;
        }
        if self.tokens.len() != 2 {
            panic!();
        }
        match [
            &self.tokens[0],
            &self.tokens[1],
        ] {
            [
                PrustiToken::Token(TokenTree::Ident(ident)),
                PrustiToken::Group(_span, Delimiter::Parenthesis, box group),
            ] => {
                if ident == "requires" {
                    Some(NestedSpec::Requires(group.clone()))
                } else if ident == "ensures" {
                    Some(NestedSpec::Ensures(group.clone()))
                } else {
                    None
                }
            }
            _ => None
        }
    }

    fn pop_group_of_nested_specs(&mut self, span: Span) -> syn::Result<Vec<NestedSpec<TokenStream>>> {
        let group_of_specs = self.pop_group(Delimiter::Bracket)
            .ok_or_else(|| syn::parse::Error::new(span, "expected nested specification in brackets"))?;
        let parsed = group_of_specs
            .split(PrustiBinaryOp::Rust(RustOp::Comma), true)
            .into_iter()
            .map(|stream| stream.pop_one_nested_spec().unwrap())
            // TODO: assert empty afterwards ...
            .map(|stream| stream.parse())
            .collect::<syn::Result<Vec<NestedSpec<TokenStream>>>>()?;
        Ok(parsed)
    }

    fn split(
        self,
        split_on: PrustiBinaryOp,
        allow_trailing: bool,
    ) -> Vec<Self> {
        if self.tokens.is_empty() {
            return vec![];
        }
        let mut res = self.tokens
            .into_iter()
            .collect::<Vec<_>>()
            .split(|token| matches!(token, PrustiToken::BinOp(_, t) if *t == split_on))
            .map(|group| Self { tokens: group.iter().cloned().collect(), source_span: self.source_span })
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
            [
                PrustiToken::BinOp(_, PrustiBinaryOp::Rust(RustOp::Comma)),
                PrustiToken::Token(TokenTree::Ident(ident)),
                PrustiToken::BinOp(_, PrustiBinaryOp::Rust(RustOp::Assign)),
                PrustiToken::Group(triggers_span, Delimiter::Bracket, box triggers),
            ] if ident == "triggers" => {
                let triggers = triggers.clone()
                    .split(PrustiBinaryOp::Rust(RustOp::Comma), true)
                    .into_iter()
                    .map(|mut stream| stream
                        .pop_group(Delimiter::Parenthesis)
                        .ok_or_else(|| syn::parse::Error::new(*triggers_span, "trigger sets must be tuples of expressions"))?
                        .split(PrustiBinaryOp::Rust(RustOp::Comma), true)
                        .into_iter()
                        .map(|stream| stream.parse())
                        .collect::<Result<Vec<_>, _>>())
                    .collect::<Result<Vec<_>, _>>();
                self.tokens.truncate(len - 4);
                triggers
            }
            _ => Ok(vec![]),
        }
    }
}

/// A specification enclosed in another specification (e.g. in spec entailments or ghost constraints)
#[derive(Debug)]
pub enum NestedSpec<T> {
    Requires(T),
    Ensures(T),
}

impl NestedSpec<PrustiTokenStream> {
    fn parse(self) -> syn::Result<NestedSpec<TokenStream>> {
        Ok(match self {
            NestedSpec::Requires(stream) => NestedSpec::Requires(stream.parse()?),
            NestedSpec::Ensures(stream) => NestedSpec::Ensures(stream.parse()?),
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
        .map(|i| TokenTree::Ident(proc_macro2::Ident::new(&format!("GA{}", i), span)))
        .collect::<Vec<_>>();
    let generic_res = TokenTree::Ident(proc_macro2::Ident::new("GR", span));

    let extract_args = (0..arg_count)
        .map(|i| TokenTree::Ident(proc_macro2::Ident::new(&format!("__extract_arg{}", i), span)))
        .collect::<Vec<_>>();
    let extract_args_decl = extract_args.iter()
        .zip(generics_args.iter())
        .map(|(ident, arg_type)| quote_spanned! { span =>
            #[prusti::spec_only]
            fn #ident<
                #(#generics_args),* ,
                #generic_res,
                F: FnOnce( #(#generics_args),* ) -> #generic_res
            >(_f: &F) -> #arg_type { unreachable!() }
        })
        .collect::<Vec<_>>();

    let preconds = contract.iter()
        .filter_map(|spec| match spec {
            NestedSpec::Requires(stream) => Some(stream.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let postconds = contract.into_iter()
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
        // TODO: refer to forall and exists with prusti_contracts:: prefix
        let trigger_sets = triggers.into_iter()
            .map(|set| {
                let triggers = TokenStream::from_iter(set.into_iter()
                    .map(|trigger| quote_spanned! { trigger.span() =>
                        #[prusti::spec_only] | #args | ( #trigger ), }));
                quote_spanned! { span => ( #triggers ) }
            })
            //.map(|set| quote_spanned! { span =>
            //    ( #( #[prusti::spec_only] | #args | ( #set ), )* ) })
            .collect::<Vec<_>>();
        match self {
            Self::Forall => quote_spanned! { body.span() => forall(
                ( #( #trigger_sets, )* ),
                #[prusti::spec_only] | #args | -> bool { ((#body): bool) }
            ) },
            Self::Exists => quote_spanned! { body.span() => exists(
                ( #( #trigger_sets, )* ),
                #[prusti::spec_only] | #args | -> bool { ((#body): bool) }
            ) },
        }
    }
}

// For Prusti-specific operators, in both [operator2] and [operator3]
// we mainly care about the spacing of the last [Punct], as this lets us
// know that the last character is not itself part of an actual Rust
// operator.
//
// "==>" should still have the expected spacing of [Joint, Joint, Alone]
// even though "==" and ">" are separate Rust operators.
fn operator2(
    op: &str,
    p1: &Punct,
    p2: &Punct,
) -> bool {
    let chars = op.chars().collect::<Vec<_>>();
    [p1.as_char(), p2.as_char()] == chars[0..2]
        && p1.spacing() == Joint
        && p2.spacing() == Alone
}

fn operator3(
    op: &str,
    p1: &Punct,
    p2: &Punct,
    p3: &Punct,
) -> bool {
    let chars = op.chars().collect::<Vec<_>>();
    [p1.as_char(), p2.as_char(), p3.as_char()] == chars[0..3]
        && p1.spacing() == Joint && p2.spacing() == Joint
        && p3.spacing() == Alone
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

    fn parse_op2(
        p1: &Punct,
        p2: &Punct,
    ) -> Option<Self> {
        let span = p1.span().join(p2.span()).unwrap();
        Some(Self::BinOp(span, if operator2("&&", p1, p2) {
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
        }))
    }

    fn parse_op3(
        p1: &Punct,
        p2: &Punct,
        p3: &Punct,
    ) -> Option<Self> {
        let span = p1.span().join(p2.span()).unwrap().join(p3.span()).unwrap();
        Some(Self::BinOp(span, if operator3("==>", p1, p2, p3) {
            PrustiBinaryOp::Implies
        } else if operator3("===", p1, p2, p3) {
            PrustiBinaryOp::SnapEq
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
        }))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PrustiBinaryOp {
    Rust(RustOp),
    Implies,
    Or,
    And,
    SnapEq,
}

impl PrustiBinaryOp {
    fn binding_power(&self) -> (u8, u8) {
        match self {
            // TODO: explain
            Self::Rust(_) => (0, 0),
            Self::Implies => (4, 3),
            Self::Or => (5, 6),
            Self::And => (7, 8),
            Self::SnapEq => (9, 10),
        }
    }

    fn translate(
        &self,
        span: Span,
        lhs: TokenStream,
        rhs: TokenStream,
    ) -> TokenStream {
        match self {
            Self::Rust(op) => op.translate(span, lhs, rhs),
            // implication is desugared into this form to avoid evaluation
            // order issues: `f(a, b)` makes Rust evaluate both `a` and `b`
            // before the `f` call
            Self::Implies => {
                // preserve span of LHS
                let not_lhs = quote_spanned! { lhs.span() => !(#lhs) };
                quote_spanned! { span => (#not_lhs || (#rhs)) }
            }
            Self::Or => quote_spanned! { span => #lhs || #rhs },
            Self::And => quote_spanned! { span => #lhs && #rhs },
            Self::SnapEq => quote_spanned! { span => snapshot_equality(#lhs, #rhs) },
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
    fn translate(
        &self,
        span: Span,
        lhs: TokenStream,
        rhs: TokenStream,
    ) -> TokenStream {
        let op = self.to_tokens(span);
        quote! { #lhs #op #rhs }
    }

    fn to_tokens(
        self,
        span: Span,
    ) -> TokenStream {
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

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! assert_error {
        ( $result:expr, $expected:expr ) => {
            {
                let _res = $result;
                assert!(_res.is_err());
                let _err = _res.unwrap_err();
                assert_eq!(_err.to_string(), $expected);
            }
        };
    }

    #[test]
    fn test_preparser() {
        assert_eq!(
            parse_prusti("a ==> b".parse().unwrap()).unwrap().to_string(),
            "(! (a) || (b))",
        );
        assert_eq!(
            parse_prusti("a ==> b ==> c".parse().unwrap()).unwrap().to_string(),
            "(! (a) || ((! (b) || (c))))",
        );
        assert_eq!(
            parse_prusti("(a ==> b && c) ==> d || e".parse().unwrap()).unwrap().to_string(),
            "(! (((! (a) || (b && c)))) || (d || e))",
        );
        assert_eq!(
            parse_prusti("forall(|x: i32| a ==> b)".parse().unwrap()).unwrap().to_string(),
            "forall (() , # [prusti :: spec_only] | x : i32 | -> bool { (((! (a) || (b))) : bool) })",
        );
        assert_eq!(
            parse_prusti("exists(|x: i32| a === b)".parse().unwrap()).unwrap().to_string(),
            "exists (() , # [prusti :: spec_only] | x : i32 | -> bool { ((snapshot_equality (a , b)) : bool) })",
        );
        assert_eq!(
            parse_prusti("forall(|x: i32| a ==> b, triggers = [(c,), (d, e)])".parse().unwrap()).unwrap().to_string(),
            "forall (((# [prusti :: spec_only] | x : i32 | (c) ,) , (# [prusti :: spec_only] | x : i32 | (d) , # [prusti :: spec_only] | x : i32 | (e) ,) ,) , # [prusti :: spec_only] | x : i32 | -> bool { (((! (a) || (b))) : bool) })",
        );
        let expr: syn::Expr = syn::parse2("assert!(a === b ==> b)".parse().unwrap()).unwrap();
        assert_eq!(
            parse_prusti(quote! { #expr }).unwrap().to_string(),
            "assert ! ((! (snapshot_equality (a , b)) || (b)))",
        );
    }

    mod ghost_constraints {
        use super::*;

        #[test]
        fn invalid_args() {
            let err_invalid_arguments = "Invalid use of macro. Two arguments expected (a trait bound `T: A + B` and multiple specifications `[requires(...), ensures(...), ...]`)";
            assert_error!(parse_ghost_constraint(quote!{ [requires(false)] }), err_invalid_arguments);
            assert_error!(parse_ghost_constraint(quote!{ }), err_invalid_arguments);
            assert_error!(parse_ghost_constraint(quote!{T: A }), err_invalid_arguments);
            assert_error!(parse_ghost_constraint(quote!{T: A, [requires(false)], "nope" }), "expected nested specification in brackets");
            assert_error!(parse_ghost_constraint(quote!{[requires(false)], T: A }), "expected nested specification in brackets");
            assert_error!(parse_ghost_constraint(quote!{T: A,  }), "expected nested specification in brackets");
            assert_error!(parse_ghost_constraint(quote!{T: A, {} }), "expected nested specification in brackets");
        }

        #[test]
        fn multiple_bounds_multiple_specs() {
            let (bounds, nested_specs) = parse_ghost_constraint(quote!{ T: A+B+Foo<i32>, [requires(true), ensures(false)]}).unwrap();

            assert_eq!(bounds.to_string(), "T : A + B + Foo < i32 >");
            match &nested_specs[0] {
                NestedSpec::Requires(ts) => assert_eq!(ts.to_string(), "true"),
                _ => panic!(),
            }
            match &nested_specs[1] {
                NestedSpec::Ensures(ts) => assert_eq!(ts.to_string(), "false"),
                _ => panic!(),
            }
        }

        #[test]
        fn no_specs() {
            let (bounds, nested_specs) = parse_ghost_constraint(quote!{ T: A, []}).unwrap();
            assert_eq!(bounds.to_string(), "T : A");
            assert!(nested_specs.is_empty());
        }

        #[test]
        fn fully_qualified_trait_path() {
            let (bounds, _) = parse_ghost_constraint(quote!{ T: path::to::A, [requires(true)]}).unwrap();
            assert_eq!(bounds.to_string(), "T : path :: to :: A");
        }
    }
}
