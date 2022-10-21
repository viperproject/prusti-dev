// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::ast::Declarations;
use proc_macro2::TokenStream;
use std::collections::HashMap;
use std::io::Write;
use quote::{quote, ToTokens, TokenStreamExt};

/// A tree of modules.
/// The tokens of each module correspond to a `mod.rs` file, and the submodules to subfolders.
pub struct ModulesTree {
    pub tokens: TokenStream,
    pub submodules: HashMap<String, ModulesTree>,
}

pub trait ToModulesTree {
    fn to_modules_tree(&self) -> ModulesTree;
}

fn declare_item_mod(item: &syn::ItemMod, tokens: &mut TokenStream) {
    for attr in &item.attrs {
        if matches!(attr.style, syn::AttrStyle::Outer) {
            attr.to_tokens(tokens);
        }
    }
    item.vis.to_tokens(tokens);
    item.mod_token.to_tokens(tokens);
    item.ident.to_tokens(tokens);
    item.semi.unwrap_or_default().to_tokens(tokens);
}

impl ToModulesTree for Declarations {
    fn to_modules_tree(&self) -> ModulesTree {
        let mut tokens = quote!{};
        for ir in &self.irs {
            // Generate tokens in the `mod.rs` file
            declare_item_mod(ir, &mut tokens);
        }
        // Generate subfolders
        let submodules = self.irs.iter()
            .map(|ir| (ir.ident.to_string(), ir.to_modules_tree()))
            .collect();
        ModulesTree {
            tokens,
            submodules
        }
    }
}

impl ToModulesTree for syn::ItemMod {
    fn to_modules_tree(&self) -> ModulesTree {
        let mut tokens = quote!{};
        let mut submodules = HashMap::new();
        if let Some((_, items)) = &self.content {
            for attr in &self.attrs {
                if matches!(attr.style, syn::AttrStyle::Inner(_)) {
                    attr.to_tokens(&mut tokens);
                }
            }
            let mut append_later = vec![];
            for item in items {
                if let syn::Item::Mod(submodule) = item {
                    // Generate tokens in the `mod.rs` file
                    declare_item_mod(submodule, &mut tokens);
                    // Generate a subfolder
                    submodules.insert(
                        submodule.ident.to_string(),
                        submodule.to_modules_tree(),
                    );
                } else {
                    append_later.push(item);
                }
            }
            tokens.append_all(append_later);
        }
        ModulesTree {
            tokens,
            submodules
        }
    }
}

impl ModulesTree {
    pub fn write_to_disk(&self, dir_path: &std::path::Path, opt_module_name: Option<&str>) {
        // Write the module file
        let curr_path;
        let file_path;
        if let Some(module_name) = opt_module_name {
            if self.submodules.is_empty() {
                file_path = dir_path.join(module_name).with_extension("rs");
                curr_path = dir_path.to_owned();
            } else {
                file_path = dir_path.join(module_name).join("mod.rs");
                curr_path = dir_path.join(module_name);
            }
        } else {
            file_path = dir_path.join("mod.rs");
            curr_path = dir_path.to_owned();
        };
        std::fs::create_dir_all(&curr_path)
            .unwrap_or_else(|err| panic!("Failed to crate folder '{}': {}", dir_path.display(), err));
        let mut file = std::fs::File::create(&file_path)
            .unwrap_or_else(|err| panic!("Failed to create file '{}': {}", file_path.display(), err));
        let gen_code = self.tokens.to_string();
        file.write_all(gen_code.as_bytes())
            .unwrap_or_else(|err| panic!("Failed to write to file '{}': {}", file_path.display(), err));
        
        // Write submodules
        for (submodule_name, submodule) in &self.submodules {
            submodule.write_to_disk(&curr_path, Some(submodule_name));
        }
    }
}
