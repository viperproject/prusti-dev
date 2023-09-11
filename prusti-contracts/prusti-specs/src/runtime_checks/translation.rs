use crate::{
    common::HasSignature,
    rewriter::AstRewriter,
    runtime_checks::{
        associated_function_info::{create_argument, Argument, AssociatedFunctionInfo},
        check_type::CheckItemType,
        error_messages,
        quantifiers::{translate_quantifier_expression, QuantifierKind},
        utils,
    },
    specifications::{common::SpecificationId, untyped},
};
use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned, ToTokens};
use syn::{parse_quote, parse_quote_spanned, spanned::Spanned, visit_mut::VisitMut};

// generates the check function that can be performed to check whether
// a contract was valid at runtime.
// Note: various modifications on the mir level are needed such that these
// checks are executed correctly.
pub(crate) fn translate_runtime_checks(
    check_type: CheckItemType,
    check_id: SpecificationId,
    // the expression of the actual contract
    tokens: TokenStream,
    // the function this contract is attached to
    item: &untyped::AnyFnItem,
) -> syn::Result<syn::Item> {
    let span = tokens.span();
    // get signature information about the associated function
    let function_info = AssociatedFunctionInfo::new(item)?;
    let mut visitor = CheckVisitor::new(function_info, check_type);
    // let check_translator = CheckTranslator::new(item, expr, lhs, check_type.clone());

    // make the expression checkable at runtime:
    let mut expr: syn::Expr = syn::parse2(tokens.clone())?;
    visitor.visit_expr_mut(&mut expr);
    // get updated function info, telling us if arguments were used in
    // old.
    let function_info = visitor.function_info;

    let item_name = syn::Ident::new(
        &format!(
            "prusti_{}_check_item_{}_{}",
            check_type,
            item.sig().ident,
            check_id
        ),
        span,
    );
    let check_id_str = check_id.to_string();
    let item_name_str = item_name.to_string();

    let forget_statements = generate_forget_statements(item, check_type, span);
    let contract_string = span.source_text().unwrap_or_else(|| tokens.to_string());
    let failure_message = format!(
        "Prusti Runtime Checks: Contract {} was violated at runtime",
        check_type.wrap_contract(&contract_string)
    );

    let failure_message_ident = error_messages::failure_message_ident(span);
    let failure_message_definition = error_messages::define_failure_message(span, &failure_message);
    let failure_message_construction = error_messages::construct_failure_message_opt(span);
    let id_attr: syn::Attribute = if check_type == CheckItemType::PledgeLhs {
        parse_quote_spanned! {item.span() =>
            #[prusti::check_before_expiry_id = #check_id_str]
        }
    } else {
        parse_quote_spanned! { item.span() =>
            #[prusti::check_id = #check_id_str]
        }
    };
    // only insert print statements if this flag is set (requires std!)
    let debug_print_stmt: Option<TokenStream> = if std::env::var("PRUSTI_DEBUG_RUNTIME_CHECKS")
        .unwrap_or_default()
        == "true"
    {
        if cfg!(feature = "std") {
            Some(quote_spanned! {span =>
                println!("check function {} is performed", #item_name_str);
            })
        } else {
            // warn user that debug information will not be emitted in no_std
            span.unwrap().warning("enabling PRUSTI_DEBUG_RUNTIME_CHECKS only has an effect if feature \"std\" is enabled too").emit();
            None
        }
    } else {
        None
    };

    let mut check_item: syn::ItemFn = parse_quote_spanned! {item.span() =>
        #[allow(unused_must_use, unused_parens, unused_variables, dead_code, non_snake_case, forgetting_copy_types)]
        #[prusti::spec_only]
        #id_attr
        fn #item_name() {
            #debug_print_stmt
            #failure_message_definition
            if !(#expr) {
                #failure_message_construction
                #forget_statements
                ::core::panic!("{}", #failure_message_ident)
            };
            // now forget about all the values since they are still owned
            // by the calling function
            #forget_statements
        }
    };
    check_item.sig.generics = item.sig().generics.clone();
    if check_type.gets_item_args() {
        check_item.sig.inputs = item.sig().inputs.clone();
    }
    if check_type.needs_result() {
        let result_arg = AstRewriter::generate_result_arg(item);
        check_item.sig.inputs.push(result_arg);
    }
    if check_type.gets_old_args() {
        let old_arg = construct_old_fnarg(&function_info, span);
        // put it inside a reference:
        check_item.sig.inputs.push(old_arg);
    }
    if let CheckItemType::PledgeRhs { .. } = check_type {
        let output_ty: syn::Type = if let syn::ReturnType::Type(_, box ty) = &item.sig().output {
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
    Ok(syn::Item::Fn(check_item))
}

pub(crate) fn translate_expression_runtime(
    tokens: TokenStream,
    check_id: SpecificationId,
    check_type: CheckItemType,
) -> syn::Result<TokenStream> {
    // a bit different since we don't generate a function, but just the
    // code-fragment performing the check
    let function_info = AssociatedFunctionInfo::empty();
    let span = tokens.span();
    let expr_str = span.source_text().unwrap_or_else(|| tokens.to_string());
    let spec_id_str = check_id.to_string();
    let failure_message = format!(
        "Prusti Runtime Checks: Contract {} was violated at runtime",
        check_type.wrap_contract(&expr_str)
    );
    let mut expr: syn::Expr = syn::parse2(tokens)?;
    let mut check_visitor = CheckVisitor::new(function_info, check_type);
    check_visitor.visit_expr_mut(&mut expr);

    let failure_message_ident = error_messages::failure_message_ident(span);
    let failure_message_definition = error_messages::define_failure_message(span, &failure_message);
    let failure_message_construction = error_messages::construct_failure_message_opt(span);
    Ok(quote_spanned! {span =>
        {
            #[prusti::check_only]
            #[prusti::spec_only]
            #[prusti::runtime_assertion]
            #[prusti::check_id = #spec_id_str]
            || -> bool {
                true
            };
            #failure_message_definition
            if !(#expr) {
                #failure_message_construction
                ::core::panic!("{}", #failure_message_ident);
            }
        }
    })
}

pub(crate) fn generate_forget_statements(
    item: &untyped::AnyFnItem,
    check_type: CheckItemType,
    span: Span,
) -> syn::Block {
    // go through all inputs, if they are not references add a forget
    // statement
    let mut stmts: Vec<syn::Stmt> = Vec::new();
    if check_type.gets_item_args() {
        for fn_arg in item.sig().inputs.clone() {
            if let Ok(arg) = create_argument(&fn_arg, 0) {
                let name: TokenStream = arg.name.parse().unwrap();
                if !arg.is_ref {
                    stmts.push(parse_quote_spanned! { span =>
                        let _ = ::core::mem::forget(#name);
                    })
                }
            }
        }
    }

    // result might be double freed too if moved into a check function
    if check_type.needs_result() {
        stmts.push(parse_quote_spanned! { span =>
            let _ = ::core::mem::forget(result);
        })
    }
    syn::Block {
        brace_token: syn::token::Brace::default(),
        stmts,
    }
}

fn construct_old_fnarg(function_info: &AssociatedFunctionInfo, span: Span) -> syn::FnArg {
    let old_values_type: syn::Type = old_values_type(span, function_info);
    parse_quote_spanned! {span =>
        old_values: #old_values_type
    }
}

/// After the visitor was run on an expression, this function
/// can be used to generate the type of the old_values tuple.
/// This type is a tuple, with the same number of fields as the original
/// function has arguments, but if the old value of an argument is never used,
/// this index in the tuple is simply a unit type. On the MIR level we can look
/// at this type, and figure out which arguments need to be cloned depending on
/// if the result type contains the argument type at the corresponding index.
fn old_values_type(span: Span, function_info: &AssociatedFunctionInfo) -> syn::Type {
    let mut old_values_type: syn::Type = parse_quote_spanned! {span => ()};
    let mut arguments = function_info.inputs.values().collect::<Vec<&Argument>>();
    // order the elements of the map by index
    arguments.sort_by(|a, b| a.index.partial_cmp(&b.index).unwrap());
    if let syn::Type::Tuple(syn::TypeTuple { elems, .. }) = &mut old_values_type {
        // start adding the elements we want to store:
        for arg in arguments {
            if arg.used_in_old {
                elems.push(arg.ty.clone());
            } else {
                // if argument is never used in old, we use a unit type
                // in the tuple (this is then also used in the mir processing
                // to determine that an argument doesn't need to be cloned)
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

pub(crate) struct CheckVisitor {
    pub function_info: AssociatedFunctionInfo,
    pub check_type: CheckItemType,
    pub within_old: bool,
    pub within_before_expiry: bool,
    /// Whether the current expression is part of the outermost
    /// expression. If yes, and we encounter a conjunction or
    /// forall quantifier, we can extend the reported error with
    /// more precise information
    is_outer: bool,
    contains_conjunction: bool,
}

impl CheckVisitor {
    pub(crate) fn new(function_info: AssociatedFunctionInfo, check_type: CheckItemType) -> Self {
        Self {
            function_info,
            check_type,
            within_old: false,
            within_before_expiry: false,
            is_outer: true,
            contains_conjunction: false,
        }
    }
}

impl VisitMut for CheckVisitor {
    fn visit_expr_mut(&mut self, expr: &mut syn::Expr) {
        let was_outer = self.is_outer;
        match expr {
            syn::Expr::Path(expr_path) => {
                // collect arguments that occurr within old expression
                // these are the ones we wanna clone
                if let Some(ident) = expr_path.path.get_ident() {
                    let name = ident.to_token_stream().to_string();
                    if let Some(arg) = self.function_info.get_mut_arg(&name) {
                        // argument used within an old expression?
                        if self.check_type.gets_old_args()
                            && (self.within_old || (!arg.is_ref && arg.is_mutable))
                        {
                            // if it was not already marked to be stored
                            // needs to be checked for indeces to be correct
                            arg.used_in_old = true;
                            // replace the identifier with the correct field access
                            let index_token: TokenStream = arg.index.to_string().parse().unwrap();
                            let new_path: syn::Expr =
                                parse_quote_spanned! { expr.span() => (old_values.#index_token)};
                            *expr = new_path;
                        }
                    } else if self.within_before_expiry && name == *"result" {
                        let new_path: syn::Expr = parse_quote_spanned! { expr.span() =>
                            result_before_expiry.0
                        };
                        *expr = new_path;
                    }
                }
            }
            syn::Expr::Call(call) => {
                self.is_outer = false;
                let path_expr = (*call.func).clone();
                let name = if let Some(name) = utils::expression_name(&path_expr) {
                    name
                } else {
                    // still visit recursively
                    syn::visit_mut::visit_expr_mut(self, expr);
                    return;
                };
                match name.as_str() {
                    ":: prusti_contracts :: old" | "prusti_contracts :: old" | "old" => {
                        // for this function we can savely try to get
                        // more precise errors about the contents
                        self.is_outer = was_outer;
                        // for prusti_assert etc we can not resolve old here
                        if self.check_type.is_inlined() {
                            syn::visit_mut::visit_expr_call_mut(self, call);
                            // just leave it as it is. resolve it on mir level
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
                    ":: prusti_contracts :: before_expiry"
                    | "prusti_contracts :: before_expiry"
                    | "before_expiry" => {
                        let sub_expr = call.args.pop();
                        *expr = sub_expr.unwrap().value().clone();
                        // will cause all variables below to be replaced by old_value.some_field
                        self.within_before_expiry = true;
                        self.visit_expr_mut(expr);
                        self.within_before_expiry = false;
                    }
                    ":: prusti_contracts :: forall" => {
                        // arguments are triggers and then the closure:
                        let quant_closure_expr: syn::Expr = call.args.last().unwrap().clone();
                        if let syn::Expr::Closure(mut expr_closure) = quant_closure_expr {
                            // since this is a conjunction, we can get more information about subexpressions failing
                            // (however, if we are in no_std, we cannot report errors recursively because of limited buffer size)
                            self.is_outer = if cfg!(feature = "std") {
                                was_outer
                            } else {
                                false
                            };
                            self.visit_expr_mut(&mut expr_closure.body);
                            let check_expr = translate_quantifier_expression(
                                &expr_closure,
                                QuantifierKind::Forall,
                                was_outer,
                            )
                            .unwrap_or_else(|err| syn::parse2(err.to_compile_error()).unwrap());
                            *expr = check_expr;
                        }
                    }
                    ":: prusti_contracts :: exists" => {
                        syn::visit_mut::visit_expr_call_mut(self, call);
                        let closure_expression: syn::Expr = call.args.last().unwrap().clone();
                        if let syn::Expr::Closure(expr_closure) = closure_expression {
                            let check_expr = translate_quantifier_expression(
                                &expr_closure,
                                QuantifierKind::Exists,
                                false,
                            )
                            .unwrap_or_else(|err| syn::parse2(err.to_compile_error()).unwrap());
                            *expr = check_expr;
                        }
                    }
                    // some cases where we want to warn users that these features
                    // will not be checked correctly: (not complete yet)
                    ":: prusti_contracts :: snapshot_equality"
                    | "prusti_contracts :: snapshot_equality"
                    | "snapshot_equality"
                    | ":: prusti_contracts :: snap"
                    | "prusti_contracts :: snap"
                    | "snap" => {
                        let message = format!(
                            "Runtime checks: Use of unsupported feature {}",
                            expr.to_token_stream()
                        );
                        expr.span().unwrap().warning(message).emit();
                    }
                    _ => syn::visit_mut::visit_expr_mut(self, expr),
                }
            }
            // If we have a conjunction on the outer level of the expression, we can
            // produce a more precise error.
            syn::Expr::Binary(syn::ExprBinary {
                left: box left,
                op: syn::BinOp::And(_),
                right: box right,
                ..
            }) if was_outer => {
                // Figure out if the sub-expressions contain even more conjunctions.
                // If yes, visiting the children of our current node will already
                // procude more precise errors than we can here.
                self.contains_conjunction = false;
                syn::visit_mut::visit_expr_mut(self, left);
                let left_contains_conjunction = self.contains_conjunction;
                self.contains_conjunction = false;
                syn::visit_mut::visit_expr_mut(self, right);
                let right_contains_conjunction = self.contains_conjunction;

                if !left_contains_conjunction {
                    let left_str = left
                        .span()
                        .source_text()
                        .unwrap_or_else(|| quote!(left).to_string());
                    let left_error_str = format!("\n\t> expression {} was violated.", left_str);
                    let new_left = error_messages::call_check_expr(left.clone(), left_error_str);
                    *left = new_left;
                }
                if !right_contains_conjunction {
                    let right_str = right
                        .span()
                        .source_text()
                        .unwrap_or_else(|| quote!(right).to_string());
                    let right_error_str = format!("\n\t> expression {} was violated.", right_str);
                    let new_right = error_messages::call_check_expr(right.clone(), right_error_str);
                    *right = new_right;
                }
                // signal to parent that it doesnt need to wrap this expression
                // into a separate check function, since it will be further split up
                self.contains_conjunction = true;
            }
            syn::Expr::Block(_) | syn::Expr::Paren(_) => {
                syn::visit_mut::visit_expr_mut(self, expr);
            }
            _ => {
                self.is_outer = false;
                syn::visit_mut::visit_expr_mut(self, expr);
            }
        }
        self.is_outer = was_outer;
    }
}
