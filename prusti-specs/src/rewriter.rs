use crate::specifications::common::SpecificationIdGenerator;
use crate::specifications::untyped;
use proc_macro2::{TokenStream, Span};
use syn::{Type, punctuated::Punctuated, Pat, Token};
use syn::spanned::Spanned;
use quote::quote_spanned;

pub(crate) struct AstRewriter {
    spec_id_generator: SpecificationIdGenerator,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpecItemType {
    Precondition,
    Postcondition,
    Predicate,
}

impl std::fmt::Display for SpecItemType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SpecItemType::Precondition => write!(f, "pre"),
            SpecItemType::Postcondition => write!(f, "post"),
            SpecItemType::Predicate => write!(f, "pred"),
        }
    }
}

impl AstRewriter {
    pub(crate) fn new() -> Self {
        Self {
            spec_id_generator: SpecificationIdGenerator::new(),
        }
    }

    pub fn generate_spec_id(&mut self) -> untyped::SpecificationId {
        self.spec_id_generator.generate()
    }

    /// Parse an assertion into a Rust expression
    pub fn process_assertion(
        &mut self,
        spec_type: SpecItemType,
        spec_id: untyped::SpecificationId,
        tokens: TokenStream,
        item: &untyped::AnyFnItem,
    ) -> syn::Result<syn::Item> {
        unimplemented!("process_assertion");
    }

    /// Parse a pledge into a Rust expression
    pub fn process_pledge(
        &mut self,
        spec_id_lhs: Option<untyped::SpecificationId>,
        spec_id_rhs: untyped::SpecificationId,
        tokens: TokenStream,
        item: &untyped::AnyFnItem,
    ) -> syn::Result<syn::Item> {
        unimplemented!("process_pledge");
    }

    /// Parse a loop invariant into a Rust expression
    pub fn process_loop(
        &mut self,
        spec_id: untyped::SpecificationId,
        tokens: TokenStream,
    ) -> TokenStream {
        unimplemented!("process_loop");
    }

    /// Parse a closure with specifications into a Rust expression
    pub fn process_closure(
        &mut self,
        inputs: Punctuated<Pat, Token![,]>,
        output: Type,
        preconds: Vec<(untyped::SpecificationId, syn::Item)>,
        postconds: Vec<(untyped::SpecificationId, syn::Item)>,
    ) -> (TokenStream, TokenStream) {
        unimplemented!("process_closure");
    }
    /// Parse an assertion into a Rust expression
    pub fn process_closure_assertion(
        &mut self,
        spec_type: SpecItemType,
        spec_id: untyped::SpecificationId,
        tokens: TokenStream,
    ) -> syn::Result<syn::Item> {
        unimplemented!("process_assertion");
    }
}

pub fn translate_empty_assertion() -> syn::Expr {
    parse_quote_spanned! {
        Span::call_site() =>
        true
    }
}

pub fn translate_pledge_rhs_only(reference: Option<syn::Expr>, rhs: syn::Expr) -> syn::Expr {
    if let Some(reference) = reference {
        parse_quote_spanned! {
            // TODO: figure out span
            Span::call_site() =>
            pledge_rhs(#reference, #rhs)
        }
    } else {
        parse_quote_spanned! {
            // TODO: figure out span
            Span::call_site() =>
            pledge_rhs(result, #rhs)
        }
    }
}

pub fn translate_pledge(reference: Option<syn::Expr>, lhs: syn::Expr, rhs: syn::Expr) -> syn::Expr {
    if let Some(reference) = reference {
        parse_quote_spanned! {
            // TODO: figure out span
            Span::call_site() =>
            pledge(#reference, #lhs, #rhs)
        }
    } else {
        parse_quote_spanned! {
            // TODO: figure out span
            Span::call_site() =>
            pledge(result, #lhs, #rhs)
        }
    }
}

pub fn translate_implication(lhs: syn::Expr, rhs: syn::Expr) -> syn::Expr {
    parse_quote_spanned! {
        lhs.span().join(rhs.span()).unwrap() =>
        implication(#lhs, #rhs)
    }
}

pub fn translate_conjunction(mut conjuncts: Vec<syn::Expr>) -> syn::Expr {
    debug_assert!(conjuncts.len() != 0, "empty conjuncts given");
    if conjuncts.len() == 1 {
        conjuncts.pop().unwrap()
    } else {
        let last = conjuncts.pop().unwrap();
        let rest = translate_conjunction(conjuncts);
        parse_quote_spanned! {
            rest.span().join(last.span()).unwrap() =>
            #rest && #last
        }
    }
}

fn args_to_tokens(mut args: Vec<(syn::Ident, syn::Type)>) -> TokenStream {
    if args.len() == 0 {
        TokenStream::new()
    } else if args.len() == 1 {
        let (ident, typ) = args.pop().unwrap();
        quote_spanned! {
            ident.span().join(typ.span()).unwrap() =>
            #ident: #typ
        }
    } else {
        let (ident, typ) = args.pop().unwrap();
        let rest = args_to_tokens(args);
        quote_spanned! {
            rest.span().join(typ.span()).unwrap() =>
            #rest, #ident: #typ
        }
    }
}

pub fn translate_spec_entailment(closure: syn::Expr, args: Vec<(syn::Ident, syn::Type)>, pres: Vec<syn::Expr>, posts: Vec<syn::Expr>) -> syn::Expr {
    parse_quote_spanned! {
        // TODO: get the right span
        Span::call_site() =>
        entailment(#closure, |#(args_to_tokens(args))| {
            {
                #(translate_conjunction(pres))
            } &&
            {
                #(translate_conjunction(posts))
            }
        })
    }
}

fn tuple_to_tokens(mut exprs: Vec<syn::Expr>) -> TokenStream {
    if exprs.len() == 0 {
        quote_spanned! {
            // TODO: get the right span
            Span::call_site() =>
            ,
        }
    } else if exprs.len() == 1 {
        let expr = exprs.pop().unwrap();
        quote_spanned! {
            expr.span() =>
            #expr,
        }
    } else {
        let last = exprs.pop().unwrap();
        let rest = tuple_to_tokens(exprs);
        quote_spanned! {
            rest.span().join(last.span()).unwrap() =>
            #rest #last,
        }
    }
}

pub fn translate_forall(vars: Vec<(syn::Ident, syn::Type)>, trigger_set: Vec<syn::Expr>, body: syn::Expr) -> syn::Expr {
    parse_quote_spanned! {
        // TODO: get the right span
        Span::call_site() =>
        forall((#(tuple_to_tokens(trigger_set))),
               |#(args_to_tokens(vars))| {
                   #body
               })
    }
}