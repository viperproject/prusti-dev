use crate::{common::HasSignature, specifications::untyped};
use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use std::collections::HashMap;
use syn::{
    parse_quote, parse_quote_spanned, punctuated::Punctuated, spanned::Spanned,
    visit_mut::VisitMut, Expr, ExprCall, FnArg,
};

pub struct CheckTranslator {
    rust_only: bool, // no translation needed if true
    within_old: bool,
    surrounding_quantifiers: Vec<Quantifier>, // list of surrounding quantifiers
    inputs: HashMap<String, Argument>,
    // each old argument that needs to be stored will be stored as a field
    // of a tuple. Need to keep track of them
    highest_old_index: usize,
}

pub fn translate_check(tokens: TokenStream, item: &untyped::AnyFnItem) -> TokenStream {
    // this unwrap can not really failed since these tokens are parsed before
    // and discarded in prusti_parse
    let mut expr = syn::parse2::<Expr>(tokens).unwrap();
    let mut visitor = CheckTranslator::new(item);
    visitor.visit_expr_mut(&mut expr);

    // after translation:
    // check if expr can be used without translating
    if visitor.rust_only {
        quote! {
            assert!(#expr);
        }
    } else {
        // to be done correctly..
        // or actually probably should not be done here..
        quote! {
            assert!(#expr);
        }
    }
}

impl<'a> CheckTranslator {
    pub fn new(item: &untyped::AnyFnItem) -> Self {
        // figure out keywords
        let inputs = item
            .sig()
            .inputs
            .iter()
            .cloned()
            .filter_map(|el| Argument::try_from(&el).ok())
            .map(|el| (el.name.clone(), el))
            .collect();
        Self {
            rust_only: true,
            within_old: false,
            surrounding_quantifiers: Vec::new(),
            inputs,
            highest_old_index: 0,
        }
    }

    pub fn old_values_type<T: Spanned>(&self, item: &T) -> syn::Type {
        let mut old_values_type: syn::Type = parse_quote_spanned! {item.span() => ()};
        if let syn::Type::Tuple(syn::TypeTuple { elems, .. }) = &mut old_values_type {
            // start adding the elements we want to store:
            for i in 0..self.highest_old_index {
                for (_, el) in &self.inputs {
                    if el.used_in_old && el.old_store_index == i {
                        elems.push(el.ty.clone());
                    }
                }
            }
            if !elems.empty_or_trailing() {
                elems.push_punct(syn::token::Comma::default());
            }
        } else {
            unreachable!();
        }
        old_values_type
    }

    pub fn construct_old_type<T: Spanned>(&self, item: &T) -> syn::FnArg {
        let old_values_type: syn::Type = self.old_values_type(item);
        parse_quote_spanned! {item.span() =>
            old_values: #old_values_type
        }
    }

    pub fn generate_store_function<T: Spanned>(
        &self,
        item: &T,
        item_name: syn::Ident,
        check_id_str: String,
    ) -> syn::ItemFn {
        let mut exprs = self
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

        parse_quote_spanned! {item.span() =>
            #[allow(unused_must_use, unused_parens, unused_variables, dead_code, non_snake_case)]
            #[prusti::spec_only]
            #[prusti::check_id = #check_id_str]
            fn #item_name() -> #old_values_type {
                return (#tuple);
            }
        }
        // parse_quote_spanned!{item.span() =>
        //     fn #item_name() -> () {
        //         ()
        //     }
        // }
        //
        // println!("store function: {:?}", res.to_token_stream().to_string());
        // res
    }
}

impl VisitMut for CheckTranslator {
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
                                quote! {&old_values.#index_token}
                            } else {
                                // unfortunately it could still be a reference..
                                // no real solution at this level
                                quote! {old_values.#index_token}
                            };
                            println!("tokens: {}", tokens);
                            let new_path = syn::parse2::<Expr>(tokens).unwrap();
                            *expr = new_path;
                        }
                    }
                    // duplicating identifiers by defining new variables within specs
                    // can break this!
                }
                syn::visit_mut::visit_expr_mut(self, expr);
            }
            Expr::Call(ExprCall { func, args, .. }) => {
                match *func.clone() {
                    Expr::Path(syn::ExprPath { path, .. }) => {
                        let name = path.to_token_stream().to_string();
                        println!("found function with name {}", name);
                        match name.as_str() {
                            ":: prusti_contracts :: old" | "prusti_contracts :: old" | "old" => {
                                let sub_expr = args.pop();
                                // remove old-call and replace with content expression
                                *expr = sub_expr.unwrap().value().clone();
                                println!("recognized old!");
                                self.rust_only = false; // no translation is not enough..
                                self.within_old = true;
                                syn::visit_mut::visit_expr_mut(self, expr);
                                // will cause all variables below to be replaced by old_value.some_field
                                self.within_old = false;
                                println!("done searching contents of old()");
                            }
                            ":: prusti_contracts :: forall" => {
                                println!("recognized forall!");
                                // extend surrounding_quantifiers correctly!
                            }
                            ":: prusti_contracts :: exists" => {
                                println!("recognized exists!");
                                // extend self.surround_quantifiers correctly!
                            }
                            _ => syn::visit_mut::visit_expr_mut(self, expr),
                        }
                    }
                    _ => syn::visit_mut::visit_expr_mut(self, expr),
                }
                // check if your next successor is an ExprCall of old:
                // the underlying expr_call must have set it! replace
                // the old function call with whatever expression is it's
                // argument!
            }
            _ => {
                syn::visit_mut::visit_expr_mut(self, expr);
            }
        }
    }
}

/// Arguments to this function / i.e. specification. This struct is meant to
/// Keep track of them and collect information about how they are used
/// within specs to correctly store them.
struct Argument {
    pub name: String,
    pub ty: syn::Type,
    pub used_in_old: bool, // set to true as soon as it occurrs within an old expr
    pub old_store_index: usize, // field in old-tuple used by this argument
    /// whether or not this field is a reference. On one hand this can be told
    /// from the type..
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
            FnArg::Receiver(_) => Err(()),
        }
    }
}

#[derive(Clone)]
enum Quantifier {
    Exists(Vec<(String, String)>),
    Forall(Vec<(String, String)>),
}
