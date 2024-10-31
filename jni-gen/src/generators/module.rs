// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{class_name::*, module_tree::*};
use std::collections::BTreeMap;

pub fn generate_module(class_names: Vec<&ClassName>) -> String {
    let mut modules = ModuleTree::default();

    for class_name in class_names {
        let components: Vec<String> = class_name
            .full_rust_components()
            .iter()
            .map(|x| x.to_string())
            .collect();
        modules = modules.insert(components);
    }

    let modules_tree = modules
        .visit(|modules| {
            let modules: BTreeMap<String, Option<String>> = modules;
            let mut res: Vec<String> = vec![];
            for (name, opt_rec_result) in modules {
                match opt_rec_result {
                    None => {
                        res.push(format!("mod {name}_wrapper;\n"));
                        res.push(format!("pub use self::{name}_wrapper::*;\n"));
                    }
                    Some(rec_result) => {
                        res.push(format!("pub mod {name} {{\n"));
                        res.push("use super::builtins;\n".to_string());
                        res.push(rec_result.to_string());
                        res.push(format!("}} // end of mod {name}\n"));
                    }
                }
            }
            res.join("")
        })
        .unwrap_or_else(|| "// No modules".to_string());

    [
        "//! Automatically generated code\n".to_string(),
        "#![allow(non_snake_case)]\n".to_string(),
        "pub mod builtins;\n".to_string(),
        modules_tree,
    ]
    .join("\n")
        + "\n"
}
