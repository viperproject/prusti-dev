use crate::specifications::common::NameGenerator;
use proc_macro2::{TokenStream, TokenTree, Group};
use quote::{quote, ToTokens};
use syn::ImplItemMethod;
use syn::spanned::Spanned;

pub fn rewrite_mod(item_mod: &mut syn::ItemMod, path: &mut syn::Path) -> syn::Result<()> {
    if item_mod.content.is_none() {
        return Ok(())
    }

    path.segments.push(syn::PathSegment { ident: item_mod.ident.clone(), arguments: syn::PathArguments::None });
    let name_generator = NameGenerator::new();
    item_mod.ident = syn::Ident::new(&name_generator.generate_mod_name(&item_mod.ident),
                                    item_mod.span());

    for item in item_mod.content.as_mut().unwrap().1.iter_mut() {
        match item {
            syn::Item::Fn(item_fn) => {
                rewrite_fn(item_fn, path);
            },
            syn::Item::Mod(inner_mod) => {
                rewrite_mod(inner_mod, path)?;
            },
            syn::Item::Verbatim(tokens) => {
                let mut new_tokens = TokenStream::new();
                for mut token in tokens.clone().into_iter() {
                    if let TokenTree::Punct(punct) = &mut token {
                        if punct.as_char() == ';' {
                            new_tokens.extend(Group::new(proc_macro2::Delimiter::Brace, TokenStream::new()).to_token_stream());
                            continue;
                        }
                    }
                    new_tokens.extend(token.to_token_stream());
                }
                let res: Result<syn::Item, _> = syn::parse2(new_tokens);
                if res.is_err() {
                    return Err(syn::Error::new(
                        item.span(),
                        "invalid function signature",
                    ))
                }

                let mut item = res.unwrap();
                if let syn::Item::Fn(item_fn) = &mut item {
                    rewrite_fn(item_fn, path);
                }
                *tokens = quote! {
                    #item
                }
            }
            syn::Item::Use(_) => {}
            _ => return Err(syn::Error::new(
                item.span(),
                "unexpected item",
            ))
        }
    }
    Ok(())
}

fn rewrite_fn(item_fn: &mut syn::ItemFn, path: &mut syn::Path) {
    let ident = &item_fn.sig.ident;
    let args = &item_fn.sig.inputs;
    item_fn.block = syn::parse_quote! {
        {
            #path :: #ident (#args);
            unimplemented!()
        }
    };

    item_fn.attrs.push(syn::parse_quote! { #[prusti::extern_spec]});
    item_fn.attrs.push(syn::parse_quote! { #[trusted] });
}

pub fn rewrite_method(
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

                let args = rewrite_method_inputs(item_ty, method);
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

pub fn rewrite_method_inputs(item_ty: &Box<syn::Type>, method: &mut ImplItemMethod) ->
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
    let name_generator = NameGenerator::new();
    let struct_name = match name_generator.generate_struct_name(item) {
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
