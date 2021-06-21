use crate::specifications::common::SpecificationIdGenerator;
use crate::specifications::untyped;
use proc_macro2::{TokenStream, Span};
use syn::{Type, punctuated::Punctuated, Pat, Token, Lit, LitBool};

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
    syn::Expr::Lit(syn::ExprLit {
        attrs: vec![],
        lit: Lit::Bool(LitBool {
            value: true,
            span: Span::call_site(),
        }),
    })
}

pub fn translate_pledge_rhs_only(reference: Option<syn::Expr>, rhs: syn::Expr) -> syn::Expr {
    unimplemented!("translate_pledge_rhs_only");
}

pub fn translate_pledge(reference: Option<syn::Expr>, lhs: syn::Expr, rhs: syn::Expr) -> syn::Expr {
    unimplemented!("translate_pledge");
}

pub fn translate_implication(lhs: syn::Expr, rhs: syn::Expr) -> syn::Expr {
    unimplemented!("translate_implication");
}

pub fn translate_conjunction(conjuncts: Vec<syn::Expr>) -> syn::Expr {
    unimplemented!("translate_conjunction");
}

pub fn translate_spec_entailment(closure: syn::Expr, args: Vec<(syn::Ident, syn::Type)>, pres: Vec<syn::Expr>, posts: Vec<syn::Expr>) -> syn::Expr {
    unimplemented!("translate_spec_entailment");
}

pub fn translate_forall(vars: Vec<(syn::Ident, syn::Type)>, trigger_set: Vec<syn::Expr>, body: syn::Expr) -> syn::Expr {
    unimplemented!("translate_forall");
}