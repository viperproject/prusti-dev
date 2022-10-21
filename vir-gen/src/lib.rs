// This Clippy chcek seems to be always wrong.
#![allow(clippy::iter_with_drain)]

use quote::quote;
use std::{
    fs::File,
    io::{Read, Write},
    mem,
    path::Path,
};
use syn::{parse_quote, parse_str};

mod ast;
mod deriver;
mod generator;
mod helpers;
mod parser;
mod pretty;
mod resolver;

/// Expands the definitions from `defs_dir` into the folder `out_dir`.
pub fn generate_vir(defs_dir: &std::path::Path, out_dir: &std::path::Path) {
    std::fs::create_dir_all(out_dir)
        .unwrap_or_else(|_| panic!("Failed to crate folder '{}'", out_dir.display()));

    // Read the declarations from the root module
    let defs_mod_path = defs_dir.join("mod.rs");
    let mut defs_mod_file = File::open(&defs_mod_path)
        .unwrap_or_else(|_| panic!("Failed to open file '{}'", defs_mod_path.display()));
    let mut defs_mod_source = String::new();
    defs_mod_file
        .read_to_string(&mut defs_mod_source)
        .unwrap_or_else(|_| panic!("Failed to read file '{}'", defs_mod_path.display()));
    let mut declarations: ast::Declarations = parse_str(&defs_mod_source)
        .unwrap_or_else(|error| panic!("Failed to parse {:?}: {}", defs_mod_path.display(), error));

    // Expand declarations
    let mut sentinel_item = parse_quote! { mod stub; };
    let mut error_tokens = proc_macro2::TokenStream::new();
    declarations.components = {
        let (expanded_components, errors) =
            parser::expand(declarations.components, defs_mod_path.to_owned());
        for error in errors {
            eprintln!("error in parsing declarations: {}", error);
            error_tokens.extend(error.to_compile_error());
        }
        expanded_components
    };
    for ir in &mut declarations.irs {
        mem::swap(ir, &mut sentinel_item);
        let (new_item, errors) = parser::expand(sentinel_item, defs_mod_path.to_owned());
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
    let generated_tokens = quote! { #declarations #error_tokens };

    // Write the tokens
    let dest_path = Path::new(&out_dir).join("mod.rs");
    let mut file = std::fs::File::create(dest_path).unwrap();
    let gen_code = pretty::pretty_print_tokenstream(&generated_tokens);
    file.write_all(&gen_code).unwrap();
}
