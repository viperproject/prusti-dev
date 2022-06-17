use syn::{punctuated::Punctuated, parse::Parser, Expr, Token, Pat, PatLit, ExprLit, Lit, Fields, parse_quote_spanned, Variant, Ident, Generics};
use log::{error};
use proc_macro2::{Span, TokenStream, TokenTree, Punct};
use quote::{quote_spanned, ToTokens};
use super::rewriter::AstRewriter;
use std::convert::TryInto;
use syn::spanned::Spanned;
use itertools::Itertools;

use crate::{
    common::{merge_generics, RewritableReceiver, SelfTypeRewriter},
    predicate::{is_predicate_macro, ParsedPredicate},
    specifications::preparser::{parse_ghost_constraint, parse_prusti, NestedSpec}, type_model,
};



pub fn rewrite_struct(attrs: TokenStream, item_struct: syn::ItemStruct) -> syn::Result<TokenStream> {

    let res = rewrite_internal_struct(attrs, item_struct);
    match res {
        Ok(result) => Ok(result),
        Err(err) => Err(err.into()),
    }
}

pub fn rewrite_enum(attrs: TokenStream, item_enum: syn::ItemEnum) -> syn::Result<TokenStream> {

    let res = rewrite_internal_enum(attrs, item_enum);
    match res {
        Ok(result) => Ok(result),
        Err(err) => Err(err.into()),
    }
}

type TypeCounterexampleResult<R> = Result<R, TypeCounterexampleError>;

#[derive(Debug)]
enum TypeCounterexampleError {

    ArgumentsDoNotMatch(proc_macro2::Span),
    WrongFirstArgument(proc_macro2::Span),
    AtLeastOneArgument(proc_macro2::Span),
    WrongNumberOfArguemnts(proc_macro2::Span),
    InvalidName(proc_macro2::Span),
    InvalidArgument(proc_macro2::Span, String, String),
    ParsingError(syn::Error),
}

impl std::convert::From<TypeCounterexampleError> for syn::Error {
    fn from(err: TypeCounterexampleError) -> Self {
        match err {
            TypeCounterexampleError::ArgumentsDoNotMatch(span) => {
                syn::Error::new(span, "Number of arguments and number of {} do not match")
            }
            TypeCounterexampleError::WrongFirstArgument(span) => {
                syn::Error::new(span, "First argument must be a string literal")
            }
            TypeCounterexampleError::AtLeastOneArgument(span) => {
                syn::Error::new(span, "At least one argument is expected")
            }
            TypeCounterexampleError::InvalidName(span) => {
                syn::Error::new(span, "Invalid argument name")
            }
            TypeCounterexampleError::InvalidArgument(span, name, arg ) => {
                syn::Error::new(span, format!("`{}` does not have a field named {}", name, arg))
            }
            TypeCounterexampleError::WrongNumberOfArguemnts(span) => {
                syn::Error::new(span, "Number of arguments are incorrect")
            }
            TypeCounterexampleError::ParsingError(parse_err) => parse_err.into(),
        }
    }
}

fn rewrite_internal_struct(attr: TokenStream, item_struct: syn::ItemStruct) -> TypeCounterexampleResult<TokenStream> {
    error!("print attr: {}", attr);
    let spec_model = check_model(&attr, item_struct.clone())?;
    if spec_model.is_empty(){
        let parser = Punctuated::<Pat, Token![,]>::parse_terminated; //parse_separated_nonempty;
    let attrs = match parser.parse(attr.clone().into()){
        Ok(result) => result,
        Err(err) => return Err(TypeCounterexampleError::ParsingError(err)),
    };
    let len = attrs.len();
    
    let (first_arg, args) = process_attr(&attrs, len)?;
    let mut rewriter = AstRewriter::new();
    let spec_id = rewriter.generate_spec_id();
    let spec_id_str = spec_id.to_string();
    error!("print spec_id: {:?}", spec_id);
    let item_span = item_struct.span();
    error!("print span: {:?}", item_span);
    let item_name = syn::Ident::new(
        &format!("prusti_print_counterexample_item_{}_{}", item_struct.ident, spec_id),
        item_span,
    );
    let mut args2: Punctuated<Pat, Token![,]> = attrs.clone().into_iter().skip(1).unique().collect::<Punctuated<Pat, Token![,]>>();
    //add trailing punctuation
    if !args2.empty_or_trailing(){
        args2.push_punct(<syn::Token![,]>::default());
    }
    error!("print item_name: {:?}", item_name);
    let typ = item_struct.ident.clone();
    let spec_item = match item_struct.fields{
        Fields::Named(_) => {
            let spec_item: syn::ItemFn = parse_quote_spanned! {item_span=>
                #[allow(unused_must_use, unused_parens, unused_variables, dead_code, non_snake_case, irrefutable_let_patterns)]
                #[prusti::spec_only]
                #[prusti::counterexample_print]
                #[prusti::spec_id = #spec_id_str]
                fn #item_name(self){
                    if let #typ{#args2 ..} = self{
                        #first_arg
                        #args
                    }
                }
            };
            spec_item
        },
        Fields::Unnamed(ref fields_unnamed) => {
                    
            //check if all args are correct
            check_validity_of_args(args2, fields_unnamed.unnamed.len() as u32, &item_struct.ident.to_string())?;
                
            let spec_item: syn::ItemFn = parse_quote_spanned! {item_span=>
                #[allow(unused_must_use, unused_parens, unused_variables, dead_code, non_snake_case, irrefutable_let_patterns)]
                #[prusti::spec_only]
                #[prusti::counterexample_print]
                #[prusti::spec_id = #spec_id_str]
                fn #item_name(self){
                    if let #typ{..} = self{
                        #first_arg
                        #args
                    }
                }
            };
            spec_item
        },
        Fields::Unit => {
            if len == 1{
                let spec_item: syn::ItemFn = parse_quote_spanned! {item_span=>
                    #[allow(unused_must_use, unused_parens, unused_variables, dead_code, non_snake_case, irrefutable_let_patterns)]
                    #[prusti::spec_only]
                    #[prusti::counterexample_print]
                    #[prusti::spec_id = #spec_id_str]
                    fn #item_name(self){
                        if let #typ{..} = self{
                            #first_arg
                        }
                    }
                };
                spec_item
            } else {
                return Err(TypeCounterexampleError::WrongNumberOfArguemnts(attr.span()));
            }
        },
    };
    
    let item_impl = generate_generics(item_struct.span().clone(), item_struct.ident.clone(), &item_struct.generics, spec_item.into_token_stream());
    
    let final_token = quote_spanned! { item_span =>
        #item_struct
        #item_impl
    };
    error!("print impl: {}", final_token);
    Ok(final_token)
    } else {
        Ok(spec_model)
    }
}


fn rewrite_internal_enum(attr: TokenStream, item_enum: syn::ItemEnum) -> TypeCounterexampleResult<TokenStream> {
    error!("print attr: {}", attr);
    let parser = Punctuated::<Pat, Token![,]>::parse_terminated; //parse_separated_nonempty;
    let attrs = match parser.parse(attr.clone().into()){
        Ok(result) => result,
        Err(err) => return Err(TypeCounterexampleError::ParsingError(err)),
    };
    let item_span = item_enum.span();
    let len = attrs.len();
    if len != 0{
        return Err(TypeCounterexampleError::WrongNumberOfArguemnts(item_span));
    }
    let mut spec_items:Vec<syn::ItemFn> = vec![]; 
    let callsite_span = Span::call_site();
    let enum_name = item_enum.ident.clone();
    let mut rewriter = AstRewriter::new();
    let spec_id = rewriter.generate_spec_id();
    let spec_id_str = spec_id.to_string(); //Does this have to be unique?
    
    for variant in &item_enum.variants{
        error!("print variant: {:?}", variant);
        if let Some(custom_print) = variant.attrs.iter().find( |attr| attr.path.get_ident().and_then(| x | Some(x.to_string())) == Some("print_counterexample".to_string())){
            error!("print custom print: {:?}", custom_print);
            let variant_name = variant.ident.clone();
            let item_span = variant.ident.span();
            let item_name = syn::Ident::new(
                &format!("prusti_print_counterexample_variant_{}_{}", variant.ident, spec_id),
                item_span,
            );
            let variant_name_str = variant_name.to_string();
            let parser = Punctuated::<Pat, Token![,]>::parse_terminated; //parse_separated_nonempty;
            let attrs = match custom_print.parse_args_with(parser){
                Ok(result) => result,
                Err(err) => return Err(TypeCounterexampleError::ParsingError(err)),
            };

            let len = attrs.len();
            error!("print attrs: {:?}", attrs);
            error!("print length: {:?}", len);
            let (first_arg, args) = process_attr(&attrs, len)?;
                match &variant.fields{
                    Fields::Named(fields_named) => {
                        let mut args2: Punctuated<Pat, Token![,]> = attrs.into_iter().skip(1).unique().collect::<Punctuated<Pat, Token![,]>>();
                        if !args2.empty_or_trailing(){
                            args2.push_punct(<syn::Token![,]>::default());
                        }
                        let spec_item: syn::ItemFn = parse_quote_spanned! {item_span=>
                            #[allow(unused_must_use, unused_parens, unused_variables, dead_code, non_snake_case, irrefutable_let_patterns)]
                            #[prusti::spec_only]
                            #[prusti::counterexample_print  = #variant_name_str]
                            #[prusti::spec_id = #spec_id_str]
                            fn #item_name(self) {
                                if let #enum_name::#variant_name{#args2 ..} = self{
                                    #first_arg
                                    #args
                                }
                            }
                        };
                        spec_items.push(spec_item);
                    },
                    Fields::Unnamed(fields_unnamed) => {
                        let args2: Punctuated<Pat, Token![,]> = attrs.into_iter().skip(1).unique().collect::<Punctuated<Pat, Token![,]>>();
                            
                            //check if all args are correct
                            check_validity_of_args(args2, fields_unnamed.unnamed.len() as u32, &item_enum.ident.to_string())?;
                            let spec_item: syn::ItemFn = parse_quote_spanned! {item_span=>
                                #[allow(unused_must_use, unused_parens, unused_variables, dead_code, non_snake_case, irrefutable_let_patterns)]
                                #[prusti::spec_only]
                                #[prusti::counterexample_print = #variant_name_str]
                                #[prusti::spec_id = #spec_id_str]
                                fn #item_name(self) {
                                    if let #enum_name::#variant_name(..) = self{
                                        #first_arg
                                        #args
                                    }
                                }
                            };
                        spec_items.push(spec_item);
                    },
                    Fields::Unit => {
                        if len == 1{
                            let spec_item: syn::ItemFn = parse_quote_spanned! {item_span=>
                                #[allow(unused_must_use, unused_parens, unused_variables, dead_code, non_snake_case, irrefutable_let_patterns)]
                                #[prusti::spec_only]
                                #[prusti::counterexample_print = #variant_name_str]
                                #[prusti::spec_id = #spec_id_str]
                                fn #item_name(self) {
                                    if let #enum_name::#variant_name = self{
                                        #first_arg
                                    }
                                }
                            };
                            spec_items.push(spec_item);
                        } else {
                            return Err(TypeCounterexampleError::WrongNumberOfArguemnts(attr.span()));
                        }
                    },
                }
        } 
    }
    error!("print new function: {:?}", spec_items);
    let mut spec_item_as_tokens = TokenStream::new();
    for x in spec_items{
        x.to_tokens(&mut spec_item_as_tokens);
    }      

    let item_impl = generate_generics(item_enum.span().clone(), item_enum.ident.clone(), &item_enum.generics, spec_item_as_tokens.into_token_stream());
    let mut item_enum = item_enum.clone();
    for variant in &mut item_enum.variants{
        //remove all macros inside the enum
        variant.attrs.retain( |attr| attr.path.get_ident().and_then(| x | Some(x.to_string())) != Some("print_counterexample".to_string()));
    }

    let final_token = quote_spanned! { item_span =>
        #item_enum
        #item_impl
    };
    error!("print impl: {}", final_token);
    Ok(final_token)
}

fn check_model(attr: &TokenStream, item_struct: syn::ItemStruct) -> TypeCounterexampleResult<TokenStream>{
    //check if type is a model
    if let Some(_) = item_struct.attrs.iter().find( |attr| attr.path.get_ident().and_then(| x | Some(x.to_string())) == Some("model".to_string())){
        let item_span = item_struct.span();
        let spec_item: syn::Item = parse_quote_spanned! {item_span=>
            #[print_counterexample(#attr)]
            #item_struct
        };
        return Ok(type_model(TokenStream::new(), spec_item.into_token_stream()))
    }
    Ok(TokenStream::new())
}

fn process_attr(attrs: &Punctuated::<Pat, Token![,]>, len: usize) -> TypeCounterexampleResult<(TokenStream, TokenStream)>{
    let mut attrs_iter = attrs.iter();
    let callsite_span = Span::call_site();
    //first arg
    let first_as_token = if let Some(text) = attrs_iter.next(){
        let span = text.span();
        match text {
            Pat::Lit(PatLit { attrs: _, expr: box Expr::Lit(ExprLit { attrs: _, lit: Lit::Str(lit_str) }) }) => {
                let value = lit_str.value();
                error!("value of text node: {}", value);
                let count = value.matches("{}").count();
                error!("count of {{}} in text node: {}", count);
                if count != len-1{
                    return Err(TypeCounterexampleError::ArgumentsDoNotMatch(span));
                }
                quote_spanned! {callsite_span=> #value;}
            },
            _ => return Err(TypeCounterexampleError::WrongFirstArgument(span)),
        }
    } else {
       return Err(TypeCounterexampleError::AtLeastOneArgument(attrs.span()));
    };
    //other args
    let args_as_token = attrs_iter.map(|pat | {
        match pat {
            Pat::Ident(pat_ident) => {
                quote_spanned! {callsite_span=> #pat_ident; }
            },
            Pat::Lit(PatLit { attrs: _, expr: box Expr::Lit(ExprLit { attrs: _, lit: Lit::Int(lit_int)})}) => {
                quote_spanned! {callsite_span=> #lit_int; }
            },
            _ => {
            let err: syn::Error = TypeCounterexampleError::InvalidName(callsite_span).into();
            err.to_compile_error()
        },  
        }
    }).collect::<TokenStream>();
    Ok((first_as_token, args_as_token))
}
fn check_validity_of_args(args: Punctuated<Pat, Token![,]>, len: u32, name: &String) -> TypeCounterexampleResult<()>{
    for arg in &args {
        if let Pat::Lit(PatLit { attrs: _, expr: box Expr::Lit(ExprLit { attrs: _, lit: Lit::Int(lit_int)})}) = arg{
            let value: u32 = match lit_int.base10_parse(){
                Ok(result) => result,
                Err(err) => return Err(TypeCounterexampleError::ParsingError(err))
            };
            error!("print value: {}", value);
            if value >= len {
                return Err(TypeCounterexampleError::InvalidArgument(arg.span(), name.to_string(), value.to_string()));
            }
        } else {
            return Err(TypeCounterexampleError::InvalidName(arg.span()));
        }
    }
    Ok(())
}

fn generate_generics(item_span: Span, typ: Ident, generics: &Generics, spec_item: TokenStream) -> syn::ItemImpl{
    let generics_idents = generics
        .params
        .iter()
        .filter_map(|generic_param| match generic_param {
            syn::GenericParam::Type(type_param) => Some(type_param.ident.clone()),
            _ => None,
        })
        .collect::<syn::punctuated::Punctuated<_, syn::Token![,]>>();
    let item_impl: syn::ItemImpl = parse_quote_spanned! {item_span=>
        impl #generics #typ <#generics_idents> {
            #spec_item
        }
    };
    item_impl
}