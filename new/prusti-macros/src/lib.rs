use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::{quote, quote_spanned};
use syn::parse::{Parse, ParseStream};
use syn::{self, parse_macro_input, punctuated::Punctuated, token, Token};

mod kw {
    syn::custom_keyword!(list);
}

#[derive(Debug, PartialEq, Eq)]
enum VisitMutTypeFunction {
    /// Do not call any funtcion.
    None,
    /// Call the given function on the element directly.
    Single(syn::Ident),
    /// Call the given function on each element of the list.
    List(syn::Ident),
}

impl Parse for VisitMutTypeFunction {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let function = if input.peek(Token![_]) {
            input.parse::<Token![_]>()?;
            VisitMutTypeFunction::None
        } else if input.peek(kw::list) {
            input.parse::<kw::list>()?;
            let content;
            syn::parenthesized!(content in input);
            VisitMutTypeFunction::List(content.parse()?)
        } else {
            VisitMutTypeFunction::Single(input.parse()?)
        };
        Ok(function)
    }
}

struct VisitMutField {
    name: syn::Ident,
    function: VisitMutTypeFunction,
}

impl Parse for VisitMutField {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let name = input.parse()?;
        input.parse::<Token![:]>()?;
        let function = input.parse()?;
        Ok(Self { name, function })
    }
}

struct VisitMutStruct {
    typ: syn::Ident,
    fields: Punctuated<VisitMutField, Token![,]>,
}

impl Parse for VisitMutStruct {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let content;
        let typ = input.parse()?;
        syn::braced!(content in input);
        let fields = content.parse_terminated(VisitMutField::parse)?;
        Ok(Self { typ, fields })
    }
}

struct VisitMutTuple {
    typ: syn::Ident,
    fields: Punctuated<VisitMutTypeFunction, Token![,]>,
}

impl Parse for VisitMutTuple {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let content;
        let typ = input.parse()?;
        syn::parenthesized!(content in input);
        let fields = content.parse_terminated(VisitMutTypeFunction::parse)?;
        Ok(Self { typ, fields })
    }
}

enum VisitMutVariant {
    Named(VisitMutStruct),
    Unnamed(VisitMutTuple),
}

impl Parse for VisitMutVariant {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        if input.peek2(token::Paren) {
            Ok(Self::Unnamed(input.parse()?))
        } else {
            Ok(Self::Named(input.parse()?))
        }
    }
}

struct VisitMutEnum {
    typ: syn::Ident,
    variants: Punctuated<VisitMutVariant, Token![,]>,
}

impl Parse for VisitMutEnum {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let content;
        let typ = input.parse()?;
        syn::braced!(content in input);
        let variants = content.parse_terminated(VisitMutVariant::parse)?;
        Ok(Self { typ, variants })
    }
}

fn generate_named_fields(
    fields: &Punctuated<VisitMutField, Token![,]>,
) -> proc_macro2::TokenStream {
    let mut field_pattern = proc_macro2::TokenStream::new();
    for VisitMutField { name, function } in fields {
        let span = name.span();
        if function == &VisitMutTypeFunction::None {
            field_pattern.extend(quote_spanned! { span =>
                #name: _,
            });
        } else {
            field_pattern.extend(quote_spanned! { span =>
                #name,
            });
        }
    }
    field_pattern
}

fn create_fn_name(type_name: &syn::Ident) -> syn::Ident {
    let mut new_name = String::from("visit");
    for ch in type_name.to_string().chars() {
        if ch.is_uppercase() {
            new_name.push('_');
            new_name.extend(ch.to_lowercase());
        } else {
            new_name.push(ch);
        }
    }
    syn::Ident::new(&new_name, Span::call_site())
}

fn generate_function_call(
    calls: &mut proc_macro2::TokenStream,
    function: &VisitMutTypeFunction,
    field_name: &syn::Ident,
) {
    let field_name_str = field_name.to_string();
    let span = field_name.span();
    match function {
        VisitMutTypeFunction::Single(function) => {
            calls.extend(quote_spanned! { span =>
                self.down(#field_name_str.to_string());
                self.#function(#field_name);
                self.up();
            });
        }
        VisitMutTypeFunction::List(function) => {
            calls.extend(quote_spanned! { span =>
                self.down(#field_name_str.to_string());
                for (i, element) in #field_name.iter_mut().enumerate() {
                    self.down(i.to_string());
                    self.#function(element);
                    self.up();
                }
                self.up();
            });
        }
        VisitMutTypeFunction::None => {}
    }
}

#[proc_macro]
pub fn visit_mut_struct(input: TokenStream) -> TokenStream {
    let pattern = parse_macro_input!(input as VisitMutStruct);
    let fn_name = create_fn_name(&pattern.typ);
    let typ = pattern.typ;
    let field_pattern = generate_named_fields(&pattern.fields);
    let mut calls = proc_macro2::TokenStream::new();
    for VisitMutField { name, function } in &pattern.fields {
        generate_function_call(&mut calls, function, name);
    }
    let fn_name_str = fn_name.to_string();
    let fn_name_opt = syn::Ident::new(&format!("{}_opt", fn_name), Span::call_site());
    (quote! {
        fn #fn_name(&mut self, node: &mut #typ) {
            trace!("[enter] {}", #fn_name_str);
            let #typ { #field_pattern } = node;
            #calls
            trace!("[exit] {}", #fn_name_str);
        }
        fn #fn_name_opt(&mut self, node: &mut Option<#typ>) {
            if let Some(node) = node {
                self.#fn_name(node);
            }
        }
    })
    .into()
}

#[proc_macro]
pub fn visit_mut_enum(input: TokenStream) -> TokenStream {
    let pattern = parse_macro_input!(input as VisitMutEnum);
    let fn_name = create_fn_name(&pattern.typ);
    let fn_name_str = fn_name.to_string();
    let enum_type = pattern.typ;
    let mut variants = proc_macro2::TokenStream::new();
    for variant in &pattern.variants {
        match variant {
            VisitMutVariant::Named(VisitMutStruct { typ, fields }) => {
                let span = typ.span();
                let field_pattern = generate_named_fields(&fields);
                let typ_str = typ.to_string();
                let mut calls = proc_macro2::TokenStream::new();
                for VisitMutField { name, function } in fields {
                    generate_function_call(&mut calls, function, name);
                }
                variants.extend(quote_spanned! { span =>
                    #enum_type::#typ { #field_pattern } => {
                        trace!("[enter] {} {}", #fn_name_str, #typ_str);
                        #calls
                        trace!("[exit] {} {}", #fn_name_str, #typ_str);
                    }
                });
            }
            VisitMutVariant::Unnamed(VisitMutTuple { typ, fields }) => {
                let span = typ.span();
                let typ_str = typ.to_string();
                if fields.is_empty() {
                    variants.extend(quote_spanned! { span =>
                        #enum_type::#typ => {}
                    });
                    continue;
                }
                let mut field_pattern = proc_macro2::TokenStream::new();
                let mut calls = proc_macro2::TokenStream::new();
                for (i, function) in fields.iter().enumerate() {
                    let field = syn::Ident::new(&format!("field_{}", i), span);
                    if function == &VisitMutTypeFunction::None {
                        field_pattern.extend(quote_spanned! { span =>
                            _,
                        });
                    } else {
                        field_pattern.extend(quote_spanned! { span =>
                            #field,
                        });
                    }
                    generate_function_call(&mut calls, function, &field);
                }
                variants.extend(quote_spanned! { span =>
                    #enum_type::#typ ( #field_pattern ) => {
                        trace!("[enter] {} {}", #fn_name_str, #typ_str);
                        #calls
                        trace!("[exit] {} {}", #fn_name_str, #typ_str);
                    }
                });
            }
        }
    }
    let fn_name_opt = syn::Ident::new(&format!("{}_opt", fn_name), Span::call_site());
    (quote! {
        fn #fn_name(&mut self, node: &mut #enum_type) {
            trace!("[enter] {}", #fn_name_str);
            match node {
                #variants
            }
            trace!("[exit] {}", #fn_name_str);
        }
        fn #fn_name_opt(&mut self, node: &mut Option<#enum_type>) {
            if let Some(node) = node {
                self.#fn_name(node);
            }
        }
    })
    .into()
}
