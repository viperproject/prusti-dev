use crate::specifications::common::{ExpressionIdGenerator, SpecificationIdGenerator, AssertionFolder, ExpressionId, SpecificationId};
use crate::specifications::untyped::{self, EncodeTypeCheck};
use proc_macro2::{Span, TokenStream};
use quote::{quote_spanned, format_ident};
use syn::spanned::Spanned;
use syn::{Type, punctuated::Punctuated, Pat, Token};
use crate::specifications::preparser::Arg;
use std::collections::HashSet;
use crate::{generate_spec_and_assertions, extract_prusti_attributes};

pub(crate) struct AstRewriter {
    expr_id_generator: ExpressionIdGenerator,
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
            expr_id_generator: ExpressionIdGenerator::new(),
            spec_id_generator: SpecificationIdGenerator::new(),
        }
    }

    pub fn generate_spec_id(&mut self) -> untyped::SpecificationId {
        self.spec_id_generator.generate()
    }

    /// Parse an assertion.
    pub fn parse_assertion(
        &mut self,
        spec_id: untyped::SpecificationId,
        tokens: TokenStream,
    ) -> syn::Result<untyped::Assertion> {
        untyped::Assertion::parse(tokens, spec_id, &mut self.expr_id_generator)
    }

    /// Parse a pledge.
    pub fn parse_pledge(
        &mut self,
        spec_id_lhs: Option<untyped::SpecificationId>,
        spec_id_rhs: untyped::SpecificationId,
        tokens: TokenStream
    ) -> syn::Result<untyped::Pledge> {
        untyped::Pledge::parse(tokens, spec_id_lhs, spec_id_rhs, &mut self.expr_id_generator)
    }

    /// Check whether function `item` contains a parameter called `keyword`. If
    /// yes, return its span.
    fn check_contains_keyword_in_params(&self, item: &untyped::AnyFnItem, keyword: &str) -> Option<Span> {
        for param in &item.sig().inputs {
            match param {
                syn::FnArg::Typed(syn::PatType {
                    pat: box syn::Pat::Ident(syn::PatIdent { ident, .. }),
                    ..
                }) => {
                    if ident == keyword {
                        return Some(param.span());
                    }
                }
                _ => {}
            }
        }
        None
    }
    fn generate_result_arg(&self, item: &untyped::AnyFnItem) -> syn::FnArg {
        let item_span = item.span();
        let output_ty = match &item.sig().output {
            syn::ReturnType::Default => parse_quote_spanned!(item_span=> ()),
            syn::ReturnType::Type(_, ty) => ty.clone(),
        };
        let fn_arg = syn::FnArg::Typed(
            syn::PatType {
                attrs: Vec::new(),
                pat: box parse_quote_spanned!(item_span=> result),
                colon_token: syn::Token![:](item.sig().output.span()),
                ty: output_ty,
            }
        );
        fn_arg
    }

    pub fn generate_abstract_coefficients(&self, assertion: &mut untyped::Assertion, fn_item: &untyped::AnyFnItem, assertion_idx: usize)
        -> Vec<syn::Item>
    {
        struct CreditFolder {
            assertion_idx: usize,
            poly_counter: usize,
            name_prefix: String,            // needs to be different for different fn_items
            added_coeffs: HashSet<String>,
        }
        impl CreditFolder {
            fn add_abstract_term_and_smaller(
                &mut self,
                term_to_add: &mut untyped::CreditPolynomialTerm,
                abstract_terms: &mut Vec<untyped::CreditPolynomialTerm>
            ) {
                // construct name of coefficient
                let mut powers_str = term_to_add.powers.iter()  // powers are ordered by var name
                    .map(|pow| format!("{}{}", pow.var.name, pow.exponent))
                    .collect::<Vec<String>>().concat();
                if powers_str.is_empty() {
                    powers_str = "0".to_string();
                }
                let coeff_name = format!("{}_{}_{}_{}", self.name_prefix, self.assertion_idx, self.poly_counter, powers_str);           //TODO: better naming?

                if !self.added_coeffs.contains(&coeff_name) {
                    let call_str = format!("{}()", coeff_name);
                    let coeff_expr: syn::Expr = syn::parse_str(&call_str)               //TODO: seems to be the simplest way to construct a syn::Expr
                        .expect("Unexpected error while parsing abstract coefficient function call");             //TODO: proper error? -> handle_result?

                    abstract_terms.push(untyped::CreditPolynomialTerm {
                        coeff_expr: untyped::Expression {
                            spec_id: term_to_add.coeff_expr.spec_id,
                            id: term_to_add.coeff_expr.id,
                            expr: coeff_expr
                        },
                        powers: term_to_add.powers.clone(),
                    });
                    self.added_coeffs.insert(coeff_name);

                    // add sub-terms with smaller exponents
                    if !term_to_add.powers.is_empty() {
                        // reduce last exponent
                        if term_to_add.powers.last().unwrap().exponent == 1 {
                            // need to remove last power
                            term_to_add.powers.remove(term_to_add.powers.len()-1);
                        }
                        else {
                            term_to_add.powers.last_mut().unwrap().exponent -= 1;
                        }

                        self.add_abstract_term_and_smaller(term_to_add, abstract_terms);
                    }
                }
            }
        }
        impl AssertionFolder<ExpressionId, syn::Expr, Arg> for CreditFolder {
            fn fold_credit_polynomial(
                &mut self,
                spec_id: SpecificationId,
                id: ExpressionId,
                credit_type: String,
                concrete_terms: Vec<untyped::CreditPolynomialTerm>,
                abstract_terms: Vec<untyped::CreditPolynomialTerm>,
            ) -> untyped::AssertionKind {

                let mut new_abstract_terms = vec![];
                for mut term in abstract_terms {
                    self.add_abstract_term_and_smaller(&mut term, &mut new_abstract_terms);
                }
                let credit_polynomial = untyped::AssertionKind::CreditPolynomial {
                    spec_id,
                    id,
                    credit_type,
                    concrete_terms,
                    abstract_terms: new_abstract_terms
                };

                self.poly_counter += 1;
                credit_polynomial
            }
        }

        let mut folder = CreditFolder {
            assertion_idx,
            poly_counter: 0,
            name_prefix: fn_item.sig().ident.to_string(),
            added_coeffs: HashSet::new()
        };
        *assertion = folder.fold_assertion(assertion.clone());

        // generate & return functions for coefficients
        let mut generated_fns = vec![];
        for coeff_name in folder.added_coeffs {
            let coeff_ident = syn::Ident::new(&coeff_name, fn_item.span());      //TODO: correct span
            //TODO: ensures necessary if use u32?
            //TODO: span correct?
            //TODO: better avoid parsing twice?
            let coeff_fn: syn::ItemFn = parse_quote_spanned! {fn_item.span()=>
                #[allow(unused_must_use, unused_variables, dead_code, unused_comparisons)]
                #[pure]
                #[trusted]
                #[ensures(result >= 0)]
                fn #coeff_ident() -> u32 {
                    unimplemented!()
                }
            };
            let mut coeff_any_fn = untyped::AnyFnItem::Fn(coeff_fn);
            println!("coeff_fn: {:?} {{ {:?} }}", coeff_any_fn.sig(), coeff_any_fn.block());
            let attributes_vec = extract_prusti_attributes(&mut coeff_any_fn).collect();
            println!("attributes: {:?}", attributes_vec);
            let (generated_spec_items, generated_attributes) =
                generate_spec_and_assertions(attributes_vec, &coeff_any_fn)
                    .expect("Internal error while creating abstract coefficient function");     //TODO: better error?

            let rewritten_coeff_fn: syn::Item = parse_quote_spanned! {coeff_any_fn.span()=>
                #(#generated_attributes)*
                #coeff_any_fn
            };
            generated_fns.push(rewritten_coeff_fn);
            generated_fns.extend(generated_spec_items);
        }

        println!("Generated fns: {:?}", generated_fns);
        generated_fns
    }

    /// Generate a dummy function for checking the given precondition, postcondition or predicate.
    ///
    /// `spec_type` should be either `"pre"`, `"post"` or `"pred"`.
    pub fn generate_spec_item_fn(
        &mut self,
        spec_type: SpecItemType,
        spec_id: untyped::SpecificationId,
        assertion: untyped::Assertion,
        item: &untyped::AnyFnItem,
    ) -> syn::Result<syn::Item> {
        if let Some(span) = self.check_contains_keyword_in_params(item, "result") {
            return Err(syn::Error::new(
                span,
                "it is not allowed to use the keyword `result` as a function argument".to_string(),
            ));
        }
        let item_span = item.span();
        let item_name = syn::Ident::new(
            &format!("prusti_{}_item_{}_{}", spec_type, item.sig().ident, spec_id),
            item_span,
        );
        let mut statements = TokenStream::new();
        assertion.encode_type_check(&mut statements);
        let spec_id_str = spec_id.to_string();
        let assertion_json = crate::specifications::json::to_json_string(&assertion);

        let mut spec_item: syn::ItemFn = parse_quote_spanned! {item_span=>
            #[allow(unused_must_use, unused_variables, dead_code)]
            #[prusti::spec_only]
            #[prusti::spec_id = #spec_id_str]
            #[prusti::assertion = #assertion_json]
            fn #item_name() {
                #statements
            }
        };
        spec_item.sig.generics = item.sig().generics.clone();
        spec_item.sig.inputs = item.sig().inputs.clone();
        if spec_type == SpecItemType::Postcondition {
            let fn_arg = self.generate_result_arg(item);
            spec_item.sig.inputs.push(fn_arg);
        }
        Ok(syn::Item::Fn(spec_item))
    }

    /// Generate statements for checking the given loop invariant.
    pub fn generate_spec_loop(
        &mut self,
        spec_id: untyped::SpecificationId,
        assertion: untyped::Assertion,
    ) -> TokenStream {
        let mut statements = TokenStream::new();
        assertion.encode_type_check(&mut statements);
        let spec_id_str = spec_id.to_string();
        let assertion_json = crate::specifications::json::to_json_string(&assertion);
        let callsite_span = Span::call_site();
        quote_spanned! {callsite_span=>
            #[allow(unused_must_use, unused_variables)]
            {
                #[prusti::spec_only]
                #[prusti::loop_body_invariant_spec]
                #[prusti::spec_id = #spec_id_str]
                #[prusti::assertion = #assertion_json]
                || {
                    #statements
                };
            }
        }
    }

    /// Generate statements for checking a closure specification.
    /// TODO: arguments, result (types are typically not known yet after parsing...)
    pub fn generate_cl_spec(
        &mut self,
        inputs: Punctuated<Pat, Token![,]>,
        output: Type,
        preconds: Vec<(untyped::SpecificationId, untyped::Assertion)>,
        postconds: Vec<(untyped::SpecificationId, untyped::Assertion)>
    ) -> (TokenStream, TokenStream) {
        let process_cond = |is_post: bool, id: &untyped::SpecificationId,
                            assertion: &untyped::Assertion| -> TokenStream
        {
            let spec_id_str = id.to_string();
            let mut encoded = TokenStream::new();
            assertion.encode_type_check(&mut encoded);
            let assertion_json = crate::specifications::json::to_json_string(&assertion);
            let name = format_ident!("prusti_{}_closure_{}", if is_post { "post" } else { "pre" }, spec_id_str);
            let callsite_span = Span::call_site();
            let result = if is_post && !inputs.empty_or_trailing() {
                quote_spanned! { callsite_span => , result: #output }
            } else if is_post {
                quote_spanned! { callsite_span => result: #output }
            } else {
                TokenStream::new()
            };
            quote_spanned! { callsite_span =>
                #[prusti::spec_only]
                #[prusti::spec_id = #spec_id_str]
                #[prusti::assertion = #assertion_json]
                fn #name(#inputs #result) {
                    #encoded
                }
            }
        };

        let mut pre_ts = TokenStream::new();
        for (id, precond) in preconds {
            pre_ts.extend(process_cond(false, &id, &precond));
        }

        let mut post_ts = TokenStream::new();
        for (id, postcond) in postconds {
            post_ts.extend(process_cond(true, &id, &postcond));
        }

        (pre_ts, post_ts)
    }
}
