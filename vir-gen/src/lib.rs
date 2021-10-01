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
            error_tokens.extend(error.to_compile_error());
        }
        expanded_components
    };
    for ir in &mut declarations.irs {
        mem::swap(ir, &mut sentinel_item);
        let (new_item, errors) = parser::expand(sentinel_item, source_file.to_owned());
        sentinel_item = new_item;
        for error in errors {
            error_tokens.extend(error.to_compile_error());
        }
        mem::swap(ir, &mut sentinel_item);
    }
    for ir in &mut declarations.irs {
        mem::swap(ir, &mut sentinel_item);
        let (new_item, errors) = resolver::expand(sentinel_item, &declarations.components);
        let (new_item_with_derives, derive_errors) = deriver::expand(new_item);
        sentinel_item = new_item_with_derives;
        for error in errors.into_iter().chain(derive_errors.into_iter()) {
            error_tokens.extend(error.to_compile_error());
        }
        mem::swap(ir, &mut sentinel_item);
    }

    quote! { #declarations #error_tokens }
}
