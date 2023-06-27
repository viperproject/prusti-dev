// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(exit_status_error)]
// This Clippy check seems to be always wrong.
#![allow(clippy::iter_with_drain)]
#![warn(clippy::disallowed_types)]

use crate::generator::ToModulesTree;
use quote::ToTokens;
use std::{fs::File, io::Read, mem, process::Command};
use syn::{parse_quote, parse_str};

mod ast;
mod deriver;
mod generator;
mod helpers;
mod parser;
mod resolver;

/// Read the definitions from `defs_dir` and write the expanded code into `out_dir`.
pub fn generate_vir(defs_dir: &std::path::Path, out_dir: &std::path::Path) {
    // Read the declarations from the root module
    let defs_mod_path = defs_dir.join("mod.rs");
    let mut defs_mod_file = File::open(&defs_mod_path)
        .unwrap_or_else(|err| panic!("Failed to open file '{}': {}", defs_mod_path.display(), err));
    let mut defs_mod_source = String::new();
    defs_mod_file
        .read_to_string(&mut defs_mod_source)
        .unwrap_or_else(|err| panic!("Failed to read file '{}': {}", defs_mod_path.display(), err));
    let mut declarations: ast::Declarations = parse_str(&defs_mod_source)
        .unwrap_or_else(|err| panic!("Failed to parse {:?}: {}", defs_mod_path.display(), err));

    // Expand declarations
    let mut error_tokens = proc_macro2::TokenStream::new();
    declarations.components = {
        let (expanded_components, errors) =
            parser::expand(declarations.components, defs_mod_path.to_owned());
        for error in errors {
            eprintln!("error in parsing declarations: {error}");
            error_tokens.extend(error.to_compile_error());
        }
        expanded_components
    };
    for ir in &mut declarations.irs {
        let mut tmp_item = parse_quote! { mod stub; };
        mem::swap(ir, &mut tmp_item);
        let (new_item, errors) = parser::expand(tmp_item, defs_mod_path.to_owned());
        tmp_item = new_item;
        for error in errors {
            eprintln!("error in expanding declarations: {error}");
            error_tokens.extend(error.to_compile_error());
        }
        mem::swap(ir, &mut tmp_item);
    }
    let mut resolved_irs = Vec::with_capacity(declarations.irs.len());
    for ir in declarations.irs {
        let (new_item, errors) = resolver::expand(ir, &declarations.components, &resolved_irs);
        for error in errors {
            eprintln!("error in resolving declarations: {error}");
            error_tokens.extend(error.to_compile_error());
        }
        resolved_irs.push(new_item);
    }
    declarations.irs = resolved_irs;
    let original_irs = declarations.irs.clone();
    for ir in &mut declarations.irs {
        let mut tmp_item = parse_quote! { mod stub; };
        mem::swap(ir, &mut tmp_item);
        let (new_item_with_derives, derive_errors) = deriver::expand(tmp_item, &original_irs);
        tmp_item = new_item_with_derives;
        for error in derive_errors {
            eprintln!("error in deriving types: {error}");
            error_tokens.extend(error.to_compile_error());
        }
        mem::swap(ir, &mut tmp_item);
    }

    // Write the tokens (and errors) to a tree of folders
    if !error_tokens.is_empty() {
        unreachable!("{}", error_tokens);
    }
    let mut modules_tree = declarations.to_modules_tree();
    error_tokens.to_tokens(&mut modules_tree.tokens);
    modules_tree.write_to_disk(out_dir, None);

    // Pretty-print the generated code
    Command::new("rustfmt")
        .arg(out_dir.join("mod.rs"))
        .status()
        .unwrap_or_else(|err| panic!("Failed to format generated code: {err}"))
        .exit_ok()
        .unwrap_or_else(|err| panic!("Formatting generated code failed with exit status {err}"));
}
