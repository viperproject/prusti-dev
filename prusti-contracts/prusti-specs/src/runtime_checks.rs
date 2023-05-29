use crate::{
    boundary_extraction::{BoundExtractor, Boundary, BoundaryKind, self},
    common::HasSignature,
    rewriter::AstRewriter,
    specifications::untyped,
};
use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use rustc_hash::{FxHashMap, FxHashSet};
use syn::{
    parse_quote, parse_quote_spanned, punctuated::Punctuated, spanned::Spanned,
    visit_mut::VisitMut, Expr, FnArg,
};

pub struct CheckTranslator {
    /// The expression within the specification
    expression: Expr,
    visitor: CheckVisitor,
}

impl CheckTranslator {
    pub fn new(item: &untyped::AnyFnItem, tokens: TokenStream) -> Self {
        // figure out keywords
        let mut expression: syn::Expr = syn::parse2::<syn::Expr>(tokens).unwrap();
        let mut visitor = CheckVisitor::new(item);
        // Does it make sense to already run the visitor here?
        visitor.visit_expr_mut(&mut expression);
        Self {
            expression,
            visitor,
        }
    }

    // generate a function that checks a pre or postcondition
    pub fn generate_check_function(
        &self,
        item: &untyped::AnyFnItem,
        item_name: syn::Ident,
        check_id_str: &String,
        has_old_arg: bool,
        has_result: bool,
    ) -> syn::ItemFn {
        let expr_to_check = &self.expression;
        let item_name_str = item_name.to_string();
        let mut check_item: syn::ItemFn = parse_quote_spanned! {item.span() =>
            #[allow(unused_must_use, unused_parens, unused_variables, dead_code, non_snake_case)]
            #[prusti::spec_only]
            #[prusti::check_id = #check_id_str]
            fn #item_name() {
                println!("check function {} is performed", #item_name_str);
                assert!(#expr_to_check);
            }
        };
        check_item.sig.generics = item.sig().generics.clone();
        // todo: make all types that are not already references, into references
        check_item.sig.inputs = item.sig().inputs.clone();
        if has_result {
            let result_arg = AstRewriter::generate_result_arg(item);
            check_item.sig.inputs.push(result_arg);
        }
        if has_old_arg {
            let old_arg = self.construct_old_fnarg(item, true);
            // put it inside a reference:
            let old_arg_ref: syn::FnArg = parse_quote_spanned! {item.span() =>
                #old_arg
            };
            check_item.sig.inputs.push(old_arg_ref);
        }
        check_item
    }

    pub fn generate_store_function(
        &self,
        item: &untyped::AnyFnItem,
        item_name: syn::Ident,
        check_id_str: String,
    ) -> syn::ItemFn {
        let mut exprs = self
            .visitor
            .inputs
            .iter()
            .filter_map(|(_, x)| if x.used_in_old { Some(x) } else { None })
            .collect::<Vec<&Argument>>();
        exprs.sort_by(|a, b| a.old_store_index.partial_cmp(&b.old_store_index).unwrap());
        let mut tuple: Punctuated<syn::Expr, syn::token::Comma> = Punctuated::new();

        exprs.iter().for_each(|el| {
            println!("field number: (control sorted!) {}", el.old_store_index);
            let name_token: TokenStream = el.name.to_string().parse().unwrap();
            let tokens_stmt: syn::Expr = parse_quote_spanned! {item.span() =>
                #name_token.clone()
            };
            tuple.push(tokens_stmt);
        });
        if !tuple.empty_or_trailing() {
            tuple.push_punct(syn::token::Comma::default());
        }
        let old_values_type = self.old_values_type(item);
        // println!("resulting tuple: {}", quote!{#tuple});

        let item_name_str = item_name.to_string();
        let mut res: syn::ItemFn = parse_quote_spanned! {item.span() =>
            #[allow(unused_must_use, unused_parens, unused_variables, dead_code, non_snake_case)]
            #[prusti::spec_only]
            #[prusti::store_id = #check_id_str]
            fn #item_name() -> #old_values_type {
                println!("store function {} is performed", #item_name_str);
                return (#tuple);
            }
        };
        // store function has the same generics and arguments as the
        // original annotated function
        res.sig.generics = item.sig().generics.clone();
        res.sig.inputs = item.sig().inputs.clone();
        res
    }

    /// After the visitor was run on an expression, this function
    /// can be used to generate the type of the old_values tuple
    /// important here is that it only contains the values that actually occurr
    /// in old-expressions and not just all arguments
    pub fn old_values_type<T: Spanned>(&self, item: &T) -> syn::Type {
        let mut old_values_type: syn::Type = parse_quote_spanned! {item.span() => ()};
        if let syn::Type::Tuple(syn::TypeTuple { elems, .. }) = &mut old_values_type {
            // start adding the elements we want to store:
            for i in 0..self.visitor.highest_old_index {
                for el in self.visitor.inputs.values() {
                    if el.used_in_old && el.old_store_index == i {
                        match &el.ty {
                            // if we have a reference, cloning will result in its inner type
                            // (usually...)
                            syn::Type::Reference(cloned_type) => {
                                elems.push(*cloned_type.elem.clone())
                            }
                            _ => elems.push(el.ty.clone()),
                        }
                    }
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

    // at the moment deref is true in all use cases. Remove
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

    // pub fn construct_function_args()

}

/// collects information about expression, but also transforms it
/// for check
pub struct CheckVisitor {
    pub rust_only: bool,
    pub within_old: bool,
    pub inputs: FxHashMap<String, Argument>,
    pub highest_old_index: usize,
}

impl CheckVisitor {
    pub fn new(item: &untyped::AnyFnItem) -> Self {
        let inputs = item
            .sig()
            .inputs
            .iter()
            .cloned()
            .filter_map(|el| Argument::try_from(&el).ok())
            .map(|el| (el.name.clone(), el))
            .collect();
        println!("collected inputs: {:?}", inputs);
        Self {
            rust_only: true,
            within_old: false,
            inputs,
            highest_old_index: 0,
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
                    println!("Found identifier: {}", ident);
                    let name = ident.to_token_stream().to_string();
                    if let Some(arg) = self.inputs.get_mut(&name) {
                        // argument used within an old expression?
                        // not already marked as used in old?
                        if self.within_old {
                            // if it was not already marked to be stored
                            // needs to be checked for indeces to be correct
                            if !arg.used_in_old {
                                println!("Marking variable {} to be stored", arg.name);
                                arg.used_in_old = true;
                                arg.old_store_index = self.highest_old_index;
                                self.highest_old_index += 1;
                            }
                            // replace the identifier with the correct field access
                            let index_token: TokenStream =
                                arg.old_store_index.to_string().parse().unwrap();
                            let tokens = if arg.is_ref {
                                // cloning will deref the value..
                                quote! {(&(&old_values.#index_token).clone())}
                            } else {
                                // unfortunately it could still be a reference..
                                // no real solution at this level
                                quote! {((&old_values.#index_token).clone())}
                            };
                            println!("tokens: {}", tokens);
                            let new_path: syn::Expr = syn::parse2(tokens).unwrap();
                            *expr = new_path;
                        }
                    } else {
                        println!("identifier {} was not found in args\n\n", name);
                    }
                    // duplicating identifiers by defining new variables within specs
                    // can break this!
                }
                syn::visit_mut::visit_expr_mut(self, expr);
            }
            Expr::Call(call)
                // func: box Expr::Path(syn::ExprPath { path, .. }),
                // ..
            => {
                // move this function, has nothing to do with boundary extraction
                let path_expr = (*call.func).clone();
                let name = if let Some(name) = boundary_extraction::expression_name(&path_expr) {
                    name
                } else {
                    // still visit recursively
                    syn::visit_mut::visit_expr_mut(self, expr);
                    println!("WARNING: Function call where name could not be extracted!\n\n");
                    return;
                };
                match name.as_str() {
                    ":: prusti_contracts :: old" | "prusti_contracts :: old" | "old" => {
                        let sub_expr = call.args.pop();
                        // remove old-call and replace with content expression
                        *expr = sub_expr.unwrap().value().clone();
                        println!("recognized old with sub_expr: {}!", quote! {#expr});
                        self.rust_only = false; // no translation is not enough..
                        self.within_old = true;
                        syn::visit_mut::visit_expr_mut(self, expr);
                        // will cause all variables below to be replaced by old_value.some_field
                        self.within_old = false;
                        println!(
                            "done searching contents of old(), expression now: {}",
                            quote! {#expr}
                        );
                    }
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
                    }
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
    pub old_store_index: usize,
    /// whether or not this field is a reference. We assume that all ref types
    /// start with & (which obviously can be wrong)
    pub is_ref: bool,
}

impl TryFrom<&FnArg> for Argument {
    type Error = ();
    fn try_from(arg: &FnArg) -> Result<Self, Self::Error> {
        match arg {
            FnArg::Typed(syn::PatType { pat, ty, .. }) => {
                if let syn::Pat::Ident(pat_ident) = *pat.clone() {
                    let is_ref = matches!(**ty, syn::Type::Reference(_));
                    let arg = Argument {
                        name: pat_ident.ident.to_string(),
                        ty: *ty.clone(),
                        used_in_old: false,
                        old_store_index: 0, // meaningless unless used_in_old is true
                        is_ref,
                    };
                    Ok(arg)
                } else {
                    Err(())
                }
            }
            FnArg::Receiver(syn::Receiver { reference, .. }) => {
                let is_ref = reference.is_some();
                let ty: syn::Type = if is_ref {
                    parse_quote! {&Self}
                } else {
                    parse_quote! {Self}
                };
                let arg = Argument {
                    name: "self".to_string(),
                    ty, // newer versions have this field! could be useful..
                    used_in_old: false,
                    old_store_index: 0,
                    is_ref,
                };
                Ok(arg)
            }
        }
    }
}

enum QuantifierKind {
    Forall,
    Exists,
}

fn translate_quantifier_expression(
    closure: &syn::ExprClosure,
    kind: QuantifierKind,
) -> syn::Expr {
    println!("translate is called");
    println!("quantifier nr args: {}", closure.inputs.len());
    let mut name_set: FxHashSet<String> = FxHashSet::default();
    let bound_vars: Vec<(String, String)> = closure
        .inputs
        .iter()
        .map(|pat: &syn::Pat| {
            println!("Pattern: {:?}", pat);
            if let syn::Pat::Type(syn::PatType {
                pat: box syn::Pat::Ident(id),
                ty: box ty,
                ..
            }) = pat
            {
                let name_str = id.to_token_stream().to_string();
                let type_str = ty.to_token_stream().to_string();
                println!("quantifier arg: {}: {}", name_str, type_str);
                name_set.insert(name_str.clone());
                (name_str, type_str)
            } else {
                // maybe we can throw a more sensible error and make the
                // check function a dummy check function
                panic!("quantifiers without type annotations can not be checked at runtime");
            }
        })
        .collect();

    let expr = *closure.body.clone();

    // initially wanted to handle multiple, but for now we dont..
    // for (name, ty) in bound_vars {
    let (name, ty) = bound_vars.get(0).unwrap();
    match ty.as_str() {
        // runtime checks for quantifiers only work for a limited set currently
        "i8" | "i16" | "i32" | "i64" | "i128" | "isize" | "u8" | "u16" | "u32" | "u64" | "u128"
        | "usize" => {
            let bounds = BoundExtractor::extract_bounds_top(expr.clone(), name, &name_set);
            println!("bounds extracted!");
            let mut upper_bound_opt = None;
            let mut lower_bound_opt = None;

            // if there are multiple variables, potentially with dependencies
            // the loops need to be in a specific order
            assert!(bounds.len() <= 2);
            let mut include_upper = true; // if we have the MAX upper limit,
            for Boundary {
                kind,
                bound,
                included,
                ..
            } in bounds.iter()
            {
                println!("Trying to define boundaries");
                                              // include it
                match *kind {
                    BoundaryKind::Upper => {
                        // first idea was to add one here if inclusive, but
                        // this can lead to overflows! Need to use ..=x syntax
                        assert!(upper_bound_opt.is_none());
                        println!("found upper bound, end included: {}", *included);
                        upper_bound_opt = Some(bound.clone());
                        include_upper = *included;
                    }
                    BoundaryKind::Lower => {
                        lower_bound_opt = if *included {
                            // lower bound works the other way around
                            Some(bound.clone())
                        } else {
                            Some(parse_quote! {
                                #bound + 1
                            })
                        }
                    }
                }
            }
            let name_token: TokenStream = name.parse().unwrap();
            let ty_token: TokenStream = ty.parse().unwrap();
            let upper_bound = upper_bound_opt.unwrap_or(parse_quote_spanned!{closure.span() =>
                #ty_token::MAX
            });
            let lower_bound = lower_bound_opt.unwrap_or(parse_quote_spanned! {closure.span() =>
                #ty_token::MIN
            });

            let range_expr: syn::Expr = if include_upper {
                parse_quote_spanned! {closure.span() =>
                    (#lower_bound)..=(#upper_bound)
                }
            } else {
                parse_quote_spanned! {closure.span() =>
                    (#lower_bound)..(#upper_bound)
                }
            };
            // maybe never turn them into strings in the first place..
            match kind {
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
                    println!("res: {}", res);
                    syn::parse2(res).unwrap()
                },
                QuantifierKind::Exists => {
                    println!("exists handled:");
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
                },
            }
        }
        _ => unimplemented!(),
    }
}
