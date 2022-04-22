// This Clippy chcek seems to be always wrong.
#![allow(clippy::iter_with_drain)]

use proc_macro2::TokenStream;
use quote::quote;
use std::mem;
use syn::parse_quote;

mod ast;
mod deriver;
mod generator;
mod helpers;
mod parser;
mod resolver;

pub fn define_vir(input: TokenStream, source_file: &std::path::Path) -> TokenStream {
    let mut declarations: ast::Declarations = syn::parse2(input)
        .unwrap_or_else(|error| panic!("Failed to parse {:?}: {}", source_file, error));
    let mut sentinel_item = parse_quote! { mod stub; };
    let mut error_tokens = proc_macro2::TokenStream::new();
    declarations.components = {
        let (expanded_components, errors) =
            parser::expand(declarations.components, source_file.to_owned());
        for error in errors {
            eprintln!("error in parsing declarations: {}", error);
            error_tokens.extend(error.to_compile_error());
        }
        expanded_components
    };
    for ir in &mut declarations.irs {
        mem::swap(ir, &mut sentinel_item);
        let (new_item, errors) = parser::expand(sentinel_item, source_file.to_owned());
        sentinel_item = new_item;
        for error in errors {
            eprintln!("error in expanding declarations: {}", error);
            error_tokens.extend(error.to_compile_error());
        }
        mem::swap(ir, &mut sentinel_item);
    }
    let mut resolved_irs = Vec::new();
    for ir in declarations.irs {
        let (new_item, errors) = resolver::expand(ir, &declarations.components, &resolved_irs);
        for error in errors {
            eprintln!("error in resolving declarations: {}", error);
            error_tokens.extend(error.to_compile_error());
        }
        resolved_irs.push(new_item);
    }
    declarations.irs = resolved_irs;
    let original_irs = declarations.irs.clone();
    for ir in &mut declarations.irs {
        mem::swap(ir, &mut sentinel_item);
        let (new_item_with_derives, derive_errors) = deriver::expand(sentinel_item, &original_irs);
        sentinel_item = new_item_with_derives;
        for error in derive_errors {
            eprintln!("error in deriving types: {}", error);
            error_tokens.extend(error.to_compile_error());
        }
        mem::swap(ir, &mut sentinel_item);
    }

    if !error_tokens.is_empty() {
        unreachable!("{:?}", error_tokens);
    }

    quote! { #declarations #error_tokens }
}
