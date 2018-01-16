use std::collections::HashMap;
use utils::*;
use module_tree::*;

pub fn generate_module(class_name_paths: Vec<String>) -> String {
    let mut modules = ModuleTree::default();

    for class_name_path in class_name_paths {
        modules = modules.insert(java_class_components(&class_name_path));
    }

    let modules_tree = modules
        .visit(|modules| {
            let modules: HashMap<String, Option<String>> = modules;
            let mut res: Vec<String> = vec![];
            for (name, opt_rec_result) in modules {
                match opt_rec_result {
                    None => {
                        res.push(format!("mod {}_wrapper;\n", name));
                        res.push(format!("pub use self::{}_wrapper::*;\n", name));
                    }
                    Some(rec_result) => {
                        res.push(format!("pub mod {} {{\n", name));
                        let code: String = rec_result.to_string();
                        res.push(code);
                        res.push(format!("}} // end of mod {}\n", name));
                    }
                }
            }
            res.join("")
        })
        .unwrap_or("// No modules".to_string());

    vec![
        "//! Automatically generated code\n".to_string(),
        "#![allow(non_snake_case)]\n".to_string(),
        modules_tree,
    ].join("\n") + "\n"
}
