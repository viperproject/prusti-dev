use crate::specifications::common::ExpressionIdGenerator;
use crate::specifications::untyped;
use proc_macro2::{Span, TokenStream};
use quote::quote;
use std::mem;
use syn::spanned::Spanned;
use syn::visit_mut::VisitMut;

pub(crate) struct AstRewriter {
    expr_id_generator: ExpressionIdGenerator,
    errors: Vec<syn::Error>,
}

impl AstRewriter {
    pub(crate) fn new() -> Self {
        Self {
            expr_id_generator: ExpressionIdGenerator::new(),
            errors: Vec::new(),
        }
    }
    fn report_error(&mut self, span: Span, msg: String) {
        self.errors.push(syn::Error::new(span, msg));
    }
    pub(crate) fn error_tokens(&self) -> TokenStream {
        self.errors
            .iter()
            .map(|error| error.to_compile_error())
            .collect()
    }
    /// Parse an assertion.
    ///
    /// Note: If this method encounters an error, it simply logs the error and
    /// returns `true`.
    fn parse_assertion(&mut self, tokens: TokenStream) -> untyped::Assertion {
        match untyped::Assertion::parse(tokens, &mut self.expr_id_generator) {
            Ok(assertion) => assertion,
            Err(err) => {
                self.errors.push(err);
                untyped::Assertion::true_assertion(&mut self.expr_id_generator)
            }
        }
    }
    /// Parse the `prusti::*` attributes of the function item into spec and
    /// remove them from the `attrs`.
    ///
    /// Note: If this method encounters an error, it simply logs the error and
    /// returns only partial specification.
    fn parse_fn_item_specs(
        &mut self,
        attrs: &mut Vec<syn::Attribute>,
    ) -> Vec<untyped::Specification> {
        let mut pre_attrs = Vec::new();
        let mut post_attrs = Vec::new();
        for attr in mem::replace(attrs, Vec::new()) {
            let first_segment = attr.path.segments.first();
            if first_segment
                .map(|first| first.ident == "prusti")
                .unwrap_or(false)
            {
                let segments = &attr.path.segments;
                if segments.len() != 2 {
                    self.report_error(
                        // FIXME: The span seems to be wrong. See the test:
                        // `prusti/tests/pass/parse/invalid_prusti_attributes.rs`
                        attr.span(),
                        "unexpected Prusti attribute; expected `prusti::requires` or `prusti::ensures`".to_string(),
                    );
                    return Vec::new();
                }
                let last_segment = &segments[1].ident;
                if last_segment == "requires" {
                    pre_attrs.push(attr);
                } else if last_segment == "ensures" {
                    post_attrs.push(attr);
                } else {
                    self.report_error(
                        // FIXME: The span seems to be wrong. See the test:
                        // `prusti/tests/pass/parse/invalid_prusti_attributes.rs`
                        last_segment.span(),
                        "unexpected Prusti attribute; expected `prusti::requires` or `prusti::ensures`".to_string(),
                    );
                    return Vec::new();
                }
            } else {
                attrs.push(attr);
            }
        }
        let mut specs = Vec::new();
        for attr in pre_attrs {
            specs.push(untyped::Specification {
                typ: untyped::SpecType::Precondition,
                assertion: self.parse_assertion(attr.tokens),
            });
        }
        for attr in post_attrs {
            specs.push(untyped::Specification {
                typ: untyped::SpecType::Postcondition,
                assertion: self.parse_assertion(attr.tokens),
            });
        }
        specs
    }
}

impl VisitMut for AstRewriter {
    fn visit_item_fn_mut(&mut self, item: &mut syn::ItemFn) {
        let specs = self.parse_fn_item_specs(&mut item.attrs);
    }
}
