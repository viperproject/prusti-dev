use crate::{
    common::HasSignature,
    rewriter::AstRewriter,
    runtime_checks::{
        associated_function_info::{create_argument, Argument, AssociatedFunctionInfo},
        check_type::CheckItemType,
        error_messages,
        visitor::CheckVisitor,
    },
    specifications::{common::SpecificationId, untyped},
};
use proc_macro2::{Span, TokenStream};
use quote::quote_spanned;
use syn::{parse_quote, parse_quote_spanned, spanned::Spanned, visit_mut::VisitMut};

// generates the check function that can be performed to check whether
// a contract was valid at runtime.
// Note: various modifications on the mir level are needed such that these
// checks are executed correctly.
pub fn translate_runtime_checks(
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
        let old_arg = construct_old_fnarg(&function_info, span, false);
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

pub fn translate_expression_runtime(
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
    // TODO: properly pass check types
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

pub fn generate_forget_statements(
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

// at the moment deref is false in all use cases. Remove
fn construct_old_fnarg(
    function_info: &AssociatedFunctionInfo,
    span: Span,
    deref: bool,
) -> syn::FnArg {
    let old_values_type: syn::Type = old_values_type(span, function_info);
    if deref {
        parse_quote_spanned! {span =>
            old_values: &#old_values_type
        }
    } else {
        parse_quote_spanned! {span =>
            old_values: #old_values_type
        }
    }
}

/// After the visitor was run on an expression, this function
/// can be used to generate the type of the old_values tuple
/// important here is that it only contains the values that actually occurr
/// in old-expressions and not just all arguments
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
