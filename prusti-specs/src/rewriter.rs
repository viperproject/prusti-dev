use crate::specifications::common::{ExpressionIdGenerator, SpecificationIdGenerator, StructNameGenerator};
use crate::specifications::untyped::{self, EncodeTypeCheck};
use proc_macro2::{Span, TokenStream};
use quote::{quote, format_ident, ToTokens};
use syn::ImplItemMethod;
use syn::spanned::Spanned;

pub(crate) struct AstRewriter {
    expr_id_generator: ExpressionIdGenerator,
    spec_id_generator: SpecificationIdGenerator,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpecItemType {
    Precondition,
    Postcondition,
}

impl std::fmt::Display for SpecItemType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SpecItemType::Precondition => write!(f, "pre"),
            SpecItemType::Postcondition => write!(f, "post"),
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
    fn check_contains_keyword_in_params(&self, item: &syn::ItemFn, keyword: &str) -> Option<Span> {
        for param in &item.sig.inputs {
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
    fn generate_result_arg(&self, item: &syn::ItemFn) -> syn::FnArg {
        let output_ty = match &item.sig.output {
            syn::ReturnType::Default => syn::parse_quote!{ () },
            syn::ReturnType::Type(_, ty) => ty.clone(),
        };
        let fn_arg = syn::FnArg::Typed(
            syn::PatType {
                attrs: Vec::new(),
                pat: box syn::parse_quote! { result },
                colon_token: syn::Token![:](item.sig.output.span()),
                ty: output_ty,
            }
        );
        fn_arg
    }
    /// Generate a dummy function for checking the given precondition or postcondition.
    ///
    /// `spec_type` should be either `"pre"` or `"post"`.
    pub fn generate_spec_item_fn(
        &mut self,
        spec_type: SpecItemType,
        spec_id: untyped::SpecificationId,
        assertion: untyped::Assertion,
        item: &syn::ItemFn,
    ) -> syn::Result<syn::Item> {
        if let Some(span) = self.check_contains_keyword_in_params(item, "result") {
            return Err(syn::Error::new(
                span,
                "it is not allowed to use the keyword `result` as a function argument".to_string(),
            ));
        }
        let item_name = syn::Ident::new(
            &format!("prusti_{}_item_{}_{}", spec_type, item.sig.ident, spec_id),
            item.span(),
        );
        let mut statements = TokenStream::new();
        assertion.encode_type_check(&mut statements);
        let spec_id_str = spec_id.to_string();
        let assertion_json = crate::specifications::json::to_json_string(&assertion);
        let mut spec_item: syn::ItemFn = syn::parse_quote! {
            #[prusti::spec_only]
            #[prusti::spec_id = #spec_id_str]
            #[prusti::assertion = #assertion_json]
            fn #item_name() {
                #statements
            }
        };
        spec_item.sig.generics = item.sig.generics.clone();
        spec_item.sig.inputs = item.sig.inputs.clone();
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
        quote! {
            #[prusti::spec_only]
            #[prusti::spec_id = #spec_id_str]
            #[prusti::assertion = #assertion_json]
            let _prusti_loop_invariant =
            {
                #statements
            };
        }
    }
    /// Generate statements for checking a closure specification.
    /// TODO: arguments, result (types are typically not known yet after parsing...)
    pub fn generate_cl_spec(
        &mut self,
        preconds: Vec<(untyped::SpecificationId,untyped::Assertion)>,
        postconds: Vec<(untyped::SpecificationId,untyped::Assertion)>
    ) -> (TokenStream, TokenStream) {
        let process_cond = |suffix: &str, count: i32, id: &untyped::SpecificationId, assertion: &untyped::Assertion, ts: &mut TokenStream| {
            let spec_id_str = id.to_string();
            let mut encoded = TokenStream::new();
            assertion.encode_type_check(&mut encoded);
            let assertion_json = crate::specifications::json::to_json_string(&assertion);
            let var_name = format_ident! ("_prusti_closure_{}{}", suffix, count.to_string());
            ts.extend(quote! {
                #[prusti::spec_only]
                #[prusti::spec_id = #spec_id_str]
                #[prusti::assertion = #assertion_json]
                let #var_name =
                {
                    #encoded
                };
            });
        };

        let mut pre_ts = TokenStream::new ();
        let mut post_ts = TokenStream::new ();
        let mut count = 0;
        for (id, precond) in preconds {
            process_cond (&"pre", count, &id, &precond, &mut pre_ts);
        }

        count = 0;
        for (id, postcond) in postconds {
            process_cond (&"post", count, &id, &postcond, &mut post_ts);
        }

        (pre_ts, post_ts)
    }
}

pub fn rewrite_extern_item_fn(
    impl_item: &mut syn::ItemImpl,
    new_ty: Box<syn::Type>,
) -> syn::Result<TokenStream> {
    let item_ty = &mut impl_item.self_ty;
    if let syn::Type::Path(type_path) = item_ty.as_mut() {
        for seg in type_path.path.segments.iter_mut() {
            if let syn::PathArguments::AngleBracketed(genargs) = &mut seg.arguments {
                genargs.colon2_token = Some(syn::token::Colon2::default());
            }
        }
    }

    for item in impl_item.items.iter_mut() {
        match item {
            syn::ImplItem::Method(method) => {
                for attr in method.attrs.iter_mut() {
                    attr.tokens = rewrite_self(attr.tokens.clone());
                }

                let args = rewrite_fn_inputs(item_ty, method);
                let ident = &method.sig.ident;

                method.attrs.push(syn::parse_quote! { #[prusti::extern_spec]});
                method.attrs.push(syn::parse_quote! { #[trusted] });

                method.block = syn::parse_quote! {
                    {
                        #item_ty :: #ident (#args);
                        unimplemented!()
                    }
                };
            }
            _ => {
                return Err(syn::Error::new(
                    item.span(),
                    "expected a method".to_string(),
                ));
            }
        }
    }
    impl_item.self_ty = new_ty;

    Ok(quote! {
        #[allow(unused_variables)]
        #[allow(dead_code)]
        #[allow(unused_must_use)]
        #impl_item
    })
}

pub fn rewrite_self(tokens: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let mut new_tokens = proc_macro2::TokenStream::new();
    for token in tokens.into_iter() {
        match token {
            proc_macro2::TokenTree::Group(group) => {
                let new_group = proc_macro2::Group::new(group.delimiter(),
                                                        rewrite_self(group.stream()));
                new_tokens.extend(new_group.to_token_stream());
            }
            proc_macro2::TokenTree::Ident(mut ident) => {
                if ident.to_string() == "self" {
                    ident = proc_macro2::Ident::new("_self", ident.span());
                }
                new_tokens.extend(ident.into_token_stream());
            }
            _ => {
                new_tokens.extend(token.into_token_stream());
            }
        }
    }
    new_tokens
}

pub fn rewrite_fn_inputs(item_ty: &Box<syn::Type>, method: &mut ImplItemMethod) ->
                           syn::punctuated::Punctuated<syn::Expr, syn::token::Comma>{
    let mut args: syn::punctuated::Punctuated<syn::Expr, syn::token::Comma> =
        syn::punctuated::Punctuated::new();

    for input in method.sig.inputs.iter_mut() {
        match input {
            syn::FnArg::Receiver(receiver) => {
                let and = if receiver.reference.is_some() {
                    quote! {&}
                } else {
                    quote! { }
                };
                let mutability = &receiver.mutability;
                let fn_arg: syn::FnArg = syn::parse_quote! { _self : #and #mutability #item_ty };
                *input = fn_arg;
                let expr: syn::Expr = syn::parse_quote! { _self };
                args.push_value(expr);
            }
            syn::FnArg::Typed(typed) => {
                if let syn::Pat::Ident(ident) = &*typed.pat {
                    let arg = &ident.ident;
                    let expr: syn::Expr = syn::parse_quote! { #arg };
                    args.push_value(expr);
                }
            }
        }
        args.push_punct(syn::token::Comma::default());
    };
    args
}

pub fn generate_new_struct(item: &syn::ItemImpl) -> syn::Result<syn::ItemStruct> {
    let name_generator = StructNameGenerator::new();
    let struct_name = match name_generator.generate(item) {
        Ok(name) => name,
        Err(msg) => return Err(syn::Error::new(
            item.span(),
            msg,
        ))
    };
    let struct_ident = syn::Ident::new(&struct_name,
    item.span(),
    );

    let mut new_struct: syn::ItemStruct = syn::parse_quote! {
        struct #struct_ident {}
    };

    new_struct.generics = item.generics.clone();
    let generics = &new_struct.generics;

    let mut fields_str: String = String::new();

    for param in generics.params.iter() {
        let field = format!("std::marker::PhantomData<{}>,", param.to_token_stream().to_string());
        fields_str.push_str(&field);
    }

    let fields : syn::FieldsUnnamed =
        syn::parse_str(&format!("({})", fields_str)).unwrap();

    new_struct.fields = syn::Fields::Unnamed(fields);
    Ok(new_struct)
}
