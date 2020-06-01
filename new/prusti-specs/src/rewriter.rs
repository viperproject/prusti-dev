use crate::specifications::common::{
    ExpressionIdGenerator, SpecificationId, SpecificationIdGenerator,
};
use crate::specifications::untyped;
use proc_macro2::{Span, TokenStream};
use std::mem;
use syn::spanned::Spanned;
use syn::visit_mut::VisitMut;

pub(crate) struct AstRewriter {
    expr_id_generator: ExpressionIdGenerator,
    spec_id_generator: SpecificationIdGenerator,
    /// The errors discovered during the specification parsing and encoding.
    errors: Vec<syn::Error>,
    /// The stack of spec items that need to be added to the encapsulating modules.
    /// TODO: Document properly how this works.
    spec_item_stack: Vec<syn::Item>,
}

impl AstRewriter {
    pub(crate) fn new() -> Self {
        Self {
            expr_id_generator: ExpressionIdGenerator::new(),
            spec_id_generator: SpecificationIdGenerator::new(),
            errors: Vec::new(),
            spec_item_stack: Vec::new(),
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
    ) -> untyped::SpecificationSet {
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
                    return untyped::SpecificationSet::Procedure(Vec::new(), Vec::new());
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
                    return untyped::SpecificationSet::Procedure(Vec::new(), Vec::new());
                }
            } else {
                attrs.push(attr);
            }
        }
        let mut pres = Vec::new();
        for attr in pre_attrs {
            pres.push(untyped::Specification {
                typ: untyped::SpecType::Precondition,
                assertion: self.parse_assertion(attr.tokens),
            });
        }
        let mut posts = Vec::new();
        for attr in post_attrs {
            posts.push(untyped::Specification {
                typ: untyped::SpecType::Postcondition,
                assertion: self.parse_assertion(attr.tokens),
            });
        }
        untyped::SpecificationSet::Procedure(pres, posts)
    }
    /// Generate the specification item and store it on the stack, so that we
    /// add it to the container such module.
    fn generate_spec_item_fn(
        &mut self,
        span: Span,
        specs: untyped::SpecificationSet,
        item: &syn::ItemFn,
    ) -> SpecificationId {
        let spec_id = self.spec_id_generator.generate();
        let item_name = syn::Ident::new(&format!("prusti_spec_item_{}", spec_id), span);
        let spec_item = syn::parse_quote! {
            fn #item_name() {
            }
        };
        self.spec_item_stack.push(spec_item);
        spec_id
    }
}

impl VisitMut for AstRewriter {
    fn visit_item_fn_mut(&mut self, item: &mut syn::ItemFn) {
        let specs = self.parse_fn_item_specs(&mut item.attrs);
        if specs.is_empty() {
            return;
        }
        let spec_id = self.generate_spec_item_fn(item.span(), specs, item);
        *item = syn::parse_quote! {
            #[prusti::spec_id(#spec_id)]
            #item
        };
    }
    fn visit_item_mod_mut(&mut self, item: &mut syn::ItemMod) {
        syn::visit_mut::visit_item_mod_mut(self, item);
        while let Some(spec_item) = self.spec_item_stack.pop() {
            let content = &mut item.content.as_mut().unwrap().1;
            content.push(spec_item);
        }
    }
    fn visit_file_mut(&mut self, file: &mut syn::File) {
        syn::visit_mut::visit_file_mut(self, file);
        while let Some(spec_item) = self.spec_item_stack.pop() {
            file.items.push(spec_item);
        }
    }
}
