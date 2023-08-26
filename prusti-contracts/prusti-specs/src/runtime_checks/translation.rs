use crate::{
    common::HasSignature,
    rewriter::{AstRewriter, SpecItemType},
    runtime_checks::{
        boundary_extraction::{self, BoundExtractor},
        check_type::CheckType,
    },
    specifications::{common::SpecificationId, untyped},
};
use proc_macro2::{Span, TokenStream};
use quote::{quote, ToTokens};
use rustc_hash::{FxHashMap, FxHashSet};
use syn::{parse_quote, parse_quote_spanned, spanned::Spanned, visit_mut::VisitMut, Expr, FnArg};

pub struct CheckTranslator {
    /// The expression within the specification (the one that will
    /// be modified by the Visitor)
    expression: Expr,
    lhs_expression: Option<Expr>,
    visitor: CheckVisitor,
    spec_type: SpecItemType,
    expr_span: Span,
    lhs_expr_span: Option<Span>,
}

/// this struct contains all possible items needed to check certain
/// specifications at runtime
pub struct RuntimeFunctions {
    /// the actual check function. For pledges, this is the check after
    /// expiration
    pub check_fn: syn::Item,
    /// for assert_after_expiry(), this is the lhs of the magic wand
    pub check_before_expiry: Option<syn::Item>,
}

/// Generates a bunch of functions that can be used to check specifications
/// at runtime.
pub fn translate_runtime_checks(
    spec_type: SpecItemType,
    check_id: SpecificationId,
    expr: TokenStream,
    lhs: Option<TokenStream>,
    item: &untyped::AnyFnItem,
) -> syn::Result<RuntimeFunctions> {
    let check_translator = CheckTranslator::new(item, expr, lhs, spec_type.clone());
    let (check_fn, check_before_expiry) = match spec_type {
        SpecItemType::Pledge => {
            // most things to generate:
            let check_fn = check_translator.generate_check_function(item, check_id, false, true);
            let check_before_expiry =
                check_translator.generate_check_function(item, check_id, true, false);

            (check_fn, Some(check_before_expiry))
        }
        SpecItemType::Postcondition => {
            let check_fn = check_translator.generate_check_function(item, check_id, false, false);
            (check_fn, None)
        }
        SpecItemType::Precondition => {
            let check_fn = check_translator.generate_check_function(item, check_id, false, false);
            (check_fn, None)
        }
        _ => unreachable!(),
    };
    syn::Result::Ok(RuntimeFunctions {
        check_fn,
        check_before_expiry,
    })
}

pub fn translate_expression_runtime(tokens: TokenStream) -> syn::Expr {
    // a bit different since we don't generate a function, but just the
    // code-fragment performing the check
    let mut expr: syn::Expr = syn::parse2(tokens).unwrap();
    let mut check_visitor = CheckVisitor::new(&dummy_fn(), CheckType::ClosureExpression);
    check_visitor.visit_expr_mut(&mut expr);
    expr
}

impl CheckTranslator {
    pub fn new(
        item: &untyped::AnyFnItem,
        tokens: TokenStream,
        lhs_tokens_opt: Option<TokenStream>,
        spec_type: SpecItemType,
    ) -> Self {
        // figure out keywords
        let expr_span = tokens.span();
        let lhs_expr_span = lhs_tokens_opt.as_ref().map(|tokens| tokens.span());
        let mut expression: syn::Expr = syn::parse2::<syn::Expr>(tokens).unwrap();
        let check_type = CheckType::from_spectype(&spec_type);
        let mut visitor = CheckVisitor::new(item, check_type);
        // Does it make sense to already run the visitor here?
        visitor.visit_expr_mut(&mut expression);
        // transform the pledge lhs too. Not sure if this is needed
        let lhs_expression = lhs_tokens_opt.map(|tokens| {
            let mut expr = syn::parse2::<syn::Expr>(tokens).unwrap();
            visitor.visit_expr_mut(&mut expr);
            expr
        });

        Self {
            expression,
            lhs_expression,
            visitor,
            spec_type,
            expr_span,
            lhs_expr_span,
        }
    }

    // generate a function that checks a pre or postcondition
    pub fn generate_check_function(
        &self,
        item: &untyped::AnyFnItem,
        check_id: SpecificationId,
        is_before_expiry_check: bool,
        before_expiry_argument: bool,
    ) -> syn::Item {
        // lhs is true for assert_on_expire only! Re-use this method to create
        // a check function for the pre-expiry check
        let lhs_str = if is_before_expiry_check { "_lhs" } else { "" };
        let item_name = syn::Ident::new(
            &format!(
                "prusti_{}{}_check_item_{}_{}",
                self.spec_type,
                lhs_str,
                item.sig().ident,
                check_id
            ),
            item.span(),
        );
        let check_id_str = check_id.to_string();
        let include_item_args = !is_before_expiry_check;
        // we differentiate items that are executed after a function
        // -> have result
        // -> have old values
        // -> moved values need to be stored too
        let executed_after = matches!(
            self.spec_type,
            SpecItemType::Postcondition | SpecItemType::Pledge
        );
        let (expr_to_check, expr_span): (syn::Expr, Span) = if is_before_expiry_check {
            // if lhs is true, there has to be a lhs expression
            if let Some(expr) = self.lhs_expression.as_ref() {
                (expr.clone(), self.lhs_expr_span.unwrap())
            } else {
                (
                    parse_quote_spanned! {item.span() =>
                        true
                    },
                    item.span(),
                )
            }
        } else {
            (self.expression.clone(), self.expr_span)
        };

        let item_name_str = item_name.to_string();
        let result_arg_opt = if executed_after {
            Some(AstRewriter::generate_result_arg(item))
        } else {
            None
        };
        let forget_statements =
            self.generate_forget_statements(item, include_item_args, executed_after);
        let contract_string = expr_span
            .source_text()
            .unwrap_or("unresolved contract".to_string());
        let failure_message = format!("Contract {} was violated at runtime", contract_string);
        let id_attr: syn::Attribute = if is_before_expiry_check {
            parse_quote_spanned! {item.span() =>
                #[prusti::check_before_expiry_id = #check_id_str]
            }
        } else {
            parse_quote_spanned! { item.span() =>
                #[prusti::check_id = #check_id_str]

            }
        };

        let mut check_item: syn::ItemFn = parse_quote_spanned! {item.span() =>
            #[allow(unused_must_use, unused_parens, unused_variables, dead_code, non_snake_case)]
            #[prusti::spec_only]
            #id_attr
            fn #item_name() {
                println!("check function {} is performed", #item_name_str);
                if !(#expr_to_check) {
                    #forget_statements
                    ::core::panic!(#failure_message)
                };
                // now forget about all the values since they are still owned
                // by the calling function
                #forget_statements
            }
        };
        check_item.sig.generics = item.sig().generics.clone();
        if include_item_args {
            check_item.sig.inputs = item.sig().inputs.clone();
        }
        if executed_after {
            check_item.sig.inputs.push(result_arg_opt.unwrap());
            let old_arg = self.construct_old_fnarg(item, false);
            // put it inside a reference:
            check_item.sig.inputs.push(old_arg);
        }
        if before_expiry_argument {
            let output_ty: syn::Type = if let syn::ReturnType::Type(_, box ty) = &item.sig().output
            {
                ty.clone()
            } else {
                // probably not our job to throw an error here? But a pledge for
                // a function with default return type does not make a lot of sense..
                parse_quote! {()}
            };
            let before_expiry_arg = parse_quote_spanned! {item.span() =>
                result_before_expiry: (#output_ty,)
            };
            check_item.sig.inputs.push(before_expiry_arg);
        }
        syn::Item::Fn(check_item)
    }

    /// After the visitor was run on an expression, this function
    /// can be used to generate the type of the old_values tuple
    /// important here is that it only contains the values that actually occurr
    /// in old-expressions and not just all arguments
    pub fn old_values_type<T: Spanned>(&self, item: &T) -> syn::Type {
        let mut old_values_type: syn::Type = parse_quote_spanned! {item.span() => ()};
        let mut arguments = self.visitor.inputs.values().collect::<Vec<&Argument>>();
        // order the elements of the map by index
        arguments.sort_by(|a, b| a.index.partial_cmp(&b.index).unwrap());
        if let syn::Type::Tuple(syn::TypeTuple { elems, .. }) = &mut old_values_type {
            // start adding the elements we want to store:
            for arg in arguments {
                if arg.used_in_old {
                    elems.push(arg.ty.clone());
                } else {
                    // if argument is never used in old, we use a unit type
                    // in the tuple
                    let unit_type: syn::Type = parse_quote_spanned! {arg.span => ()};
                    elems.push(unit_type);
                }
            }
            // if brackets contain only one type, it's not a tuple. Therefore
            // make a comma at the end, if there is at least one element
            if !elems.empty_or_trailing() {
                elems.push_punct(syn::token::Comma::default());
            }
        } else {
            unreachable!();
        }
        old_values_type
    }

    // at the moment deref is false in all use cases. Remove
    pub fn construct_old_fnarg<T: Spanned>(&self, item: &T, deref: bool) -> syn::FnArg {
        let old_values_type: syn::Type = self.old_values_type(item);
        if deref {
            parse_quote_spanned! {item.span() =>
                old_values: &#old_values_type
            }
        } else {
            parse_quote_spanned! {item.span() =>
                old_values: #old_values_type
            }
        }
    }

    pub fn generate_forget_statements(
        &self,
        item: &untyped::AnyFnItem,
        forget_item_args: bool,
        has_result_arg: bool,
    ) -> syn::Block {
        // go through all inputs, if they are not references add a forget
        // statement
        let mut stmts: Vec<syn::Stmt> = Vec::new();
        if forget_item_args {
            for fn_arg in item.sig().inputs.clone() {
                if let Ok(arg) = create_argument(&fn_arg, 0) {
                    let name: TokenStream = arg.name.parse().unwrap();
                    if !arg.is_ref {
                        stmts.push(parse_quote! {
                            ::core::mem::forget(#name);
                        })
                    }
                }
            }
        }

        // result might be double freed too if moved into a check function
        if has_result_arg {
            stmts.push(parse_quote! {
                std::mem::forget(result);
            })
        }
        syn::Block {
            brace_token: syn::token::Brace::default(),
            stmts,
        }
    }
}

/// collects information about expression, but also transforms it
/// for check
pub struct CheckVisitor {
    pub within_old: bool,
    pub within_before_expiry: bool,
    pub inputs: FxHashMap<String, Argument>,
    pub highest_old_index: usize,
    pub check_type: CheckType,
}

impl CheckVisitor {
    pub fn new(item: &untyped::AnyFnItem, check_type: CheckType) -> Self {
        let inputs = item
            .sig()
            .inputs
            .iter()
            .enumerate()
            .filter_map(|(id, el)| create_argument(el, id).ok())
            .map(|el| (el.name.clone(), el))
            .collect();
        Self {
            within_old: false,
            within_before_expiry: false,
            inputs,
            highest_old_index: 0,
            check_type,
        }
    }
}

impl VisitMut for CheckVisitor {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        match expr {
            Expr::Path(expr_path) => {
                // collect arguments that occurr within old expression
                // these are the ones we wanna clone
                if let Some(ident) = expr_path.path.get_ident() {
                    let name = ident.to_token_stream().to_string();
                    if self.check_type.is_closure() && self.within_old {
                        // let tokens = parse_quote! {old(#expr)};
                        // *expr = tokens;
                    } else if let Some(arg) = self.inputs.get_mut(&name) {
                        // argument used within an old expression?
                        // not already marked as used in old?
                        if self.check_type.has_old_tuple() && (self.within_old || (!arg.is_ref && arg.is_mutable)) {
                            // if it was not already marked to be stored
                            // needs to be checked for indeces to be correct
                            arg.used_in_old = true;
                            // replace the identifier with the correct field access
                            let index_token: TokenStream =
                                arg.index.to_string().parse().unwrap();
                            let tokens = quote! {(old_values.#index_token)};
                            let new_path: syn::Expr = syn::parse2(tokens).unwrap();
                            *expr = new_path;
                        }
                    } else if self.within_before_expiry && name == *"result" {
                        let new_path: syn::Expr = parse_quote! {
                            result_before_expiry.0
                        };
                        *expr = new_path;
                    }
                }
            }
            Expr::Call(call)
                // func: box Expr::Path(syn::ExprPath { path, .. }),
                // ..
            => {
                let path_expr = (*call.func).clone();
                // move this function, has nothing to do with boundary extraction
                let name = if let Some(name) = boundary_extraction::expression_name(&path_expr) {
                    name
                } else {
                    // still visit recursively
                    syn::visit_mut::visit_expr_mut(self, expr);
                    return;
                };
                match name.as_str() {
                    ":: prusti_contracts :: old" | "prusti_contracts :: old" | "old" => {
                        if self.check_type.is_closure() {
                            syn::visit_mut::visit_expr_call_mut(self, call);
                            // just leave it as it is.. resolve it on mir level
                        } else {
                            let sub_expr = call.args.pop();
                            // remove old-call and replace with content expression
                            *expr = sub_expr.unwrap().value().clone();
                            self.within_old = true;
                            self.visit_expr_mut(expr);
                            // will cause all variables below to be replaced by old_value.some_field
                            self.within_old = false;
                        }
                    }
                    ":: prusti_contracts :: before_expiry" | "prusti_contracts :: before_expiry" | "before_expiry" => {
                        let sub_expr = call.args.pop();
                        *expr = sub_expr.unwrap().value().clone();
                        self.within_before_expiry = true;
                        self.visit_expr_mut(expr);
                        // will cause all variables below to be replaced by old_value.some_field
                        self.within_before_expiry = false;
                    },
                    ":: prusti_contracts :: forall" => {
                        syn::visit_mut::visit_expr_call_mut(self, call);
                        // arguments are triggers and then the closure:
                        let quant_closure_expr: syn::Expr = call.args.last().unwrap().clone();
                        if let syn::Expr::Closure(expr_closure) = quant_closure_expr {
                            // we are throwing away any triggers
                            // extract all the relevant information, construct a
                            // new expression
                            let check_expr = translate_quantifier_expression(
                                &expr_closure,
                                QuantifierKind::Forall,
                            );
                            *expr = check_expr;
                        }                    }
                    ":: prusti_contracts :: exists" => {
                        syn::visit_mut::visit_expr_call_mut(self, call);
                        // extend self.surround_quantifiers correctly!
                        let closure_expression: syn::Expr = call.args.last().unwrap().clone();
                        if let syn::Expr::Closure(expr_closure) = closure_expression {
                            let check_expr = translate_quantifier_expression(
                                &expr_closure,
                                QuantifierKind::Exists,
                            );
                            *expr = check_expr
                        }
                    },
                    _ => syn::visit_mut::visit_expr_mut(self, expr),
                }
            }
            _ => {
                syn::visit_mut::visit_expr_mut(self, expr);
            }
        }
    }
}

/// Arguments to a function / i.e. specification. This struct is meant to
/// Keep track of them and collect information about how they are used
/// within specs to correctly store their old values for runtime checks.
#[derive(Debug)]
pub struct Argument {
    /// name of the argument (stays the same from original function to specks to checks)
    pub name: String,
    /// the type of this argument. If it's none, then only because this is a Self
    /// type.
    pub ty: syn::Type,
    /// whether this value occurrs in an old expression. Don't want to clone
    /// all args, since then they have to implement clone() and the type
    /// resulting from cloning them must be known at ast level
    pub used_in_old: bool,
    /// field in old-tuple (old_values.X) where this argument will be stored
    pub index: usize,
    /// whether or not this field is a reference. We assume that all ref types
    /// start with & (which obviously can be wrong)
    pub is_ref: bool,
    pub is_mutable: bool,
    pub span: Span,
}

fn create_argument(arg: &FnArg, index: usize) -> Result<Argument, ()> {
    let span = arg.span();
    match arg {
        FnArg::Typed(syn::PatType { pat, ty, .. }) => {
            if let syn::Pat::Ident(pat_ident) = *pat.clone() {
                let is_mutable = pat_ident.mutability.is_some();

                let is_ref = matches!(**ty, syn::Type::Reference(_));
                let arg = Argument {
                    name: pat_ident.ident.to_string(),
                    ty: *ty.clone(),
                    used_in_old: false,
                    index,
                    is_ref,
                    is_mutable,
                    span,
                };
                Ok(arg)
            } else {
                // TODO: proper error message
                Err(())
            }
        }
        FnArg::Receiver(syn::Receiver {
            reference,
            mutability,
            ..
        }) => {
            let is_ref = reference.is_some();
            let is_mutable = mutability.is_some();
            let ty: syn::Type = if is_ref {
                parse_quote! {&Self}
            } else {
                parse_quote! {Self}
            };
            let arg = Argument {
                name: "self".to_string(),
                ty, // newer versions have this field! could be useful..
                used_in_old: false,
                index,
                is_ref,
                is_mutable,
                span,
            };
            Ok(arg)
        }
    }
}

enum QuantifierKind {
    Forall,
    Exists,
}

fn translate_quantifier_expression(closure: &syn::ExprClosure, kind: QuantifierKind) -> syn::Expr {
    let mut name_set: FxHashSet<String> = FxHashSet::default();
    // the variables that occurr as arguments
    let bound_vars: Vec<(String, syn::Type)> = closure
        .inputs
        .iter()
        .map(|pat: &syn::Pat| {
            if let syn::Pat::Type(syn::PatType {
                pat: box syn::Pat::Ident(id),
                ty: box ty,
                ..
            }) = pat
            {
                let name_str = id.to_token_stream().to_string();
                name_set.insert(name_str.clone());
                (name_str, ty.clone())
            } else {
                // maybe we can throw a more sensible error and make the
                // check function a dummy check function
                panic!("quantifiers without type annotations can not be checked at runtime");
            }
        })
        .collect();

    // look for the runtime_quantifier_bounds attribute:
    let manual_bounds = BoundExtractor::manual_bounds(closure.clone(), bound_vars.clone());
    let bounds = manual_bounds
        .unwrap_or_else(|| BoundExtractor::derive_ranges(*closure.body.clone(), bound_vars));

    let mut expr = *closure.body.clone();

    for ((name, _), range_expr) in bounds.iter().rev() {
        let name_token: TokenStream = name.parse().unwrap();

        // maybe never turn them into strings in the first place..
        expr = match kind {
            QuantifierKind::Forall => {
                let res = quote! {
                    {
                        let mut holds_forall = true;
                        for #name_token in #range_expr {
                            if !(#expr) {
                                holds_forall = false;
                                break;
                            }
                        }
                        holds_forall
                    }
                };
                syn::parse2(res).unwrap()
            }
            QuantifierKind::Exists => {
                let res = quote! {
                {
                    let mut exists = false;
                    for #name_token in #range_expr {
                        if #expr {
                            exists = true;
                            break;
                        }
                    }
                    exists
                }
                };
                syn::parse2(res).unwrap()
            }
        }
    }
    expr
}

pub fn dummy_fn() -> untyped::AnyFnItem {
    parse_quote! {
        fn x(){}
    }
}
