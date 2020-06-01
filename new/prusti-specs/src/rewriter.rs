use crate::specifications::untyped;
use proc_macro2::Span;
use proc_macro2::TokenStream;
use quote::quote;
use std::mem;
use syn::spanned::Spanned;
use syn::visit_mut::VisitMut;

pub(crate) struct AstRewriter {
    errors: Vec<syn::Error>,
}

impl AstRewriter {
    pub(crate) fn new() -> Self {
        Self { errors: Vec::new() }
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
    fn parse_fn_item_specs(
        &mut self,
        attrs: &mut Vec<syn::Attribute>,
    ) -> Vec<untyped::Specification> {
        let mut pre_attrs = Vec::new();
        let mut post_attrs = Vec::new();
        let mut all_attrs = Vec::new();
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
                all_attrs.push(attr);
            }
        }
        unimplemented!(" HERE ");
    }
}

impl VisitMut for AstRewriter {
    fn visit_item_fn_mut(&mut self, item: &mut syn::ItemFn) {
        let specs = self.parse_fn_item_specs(&mut item.attrs);
    }
}
