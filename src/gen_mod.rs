use std::collections::HashMap;
use utils::*;
use module_tree::*;

pub fn generate_target_mod_code(targets: &Vec<String>) -> String {
    let mut modules = ModuleTree::default();

    for target in targets {
        modules = modules.insert(java_target_components(target));
    }

    let modules_tree = modules
        .visit(|modules| {
            let modules: HashMap<String, Option<String>> = modules;
            let mut res: Vec<String> = vec![];
            for (name, opt_rec_result) in modules {
                match opt_rec_result {
                    None => {
                        res.push(format!("pub mod {};\n", name));
                    }
                    Some(rec_result) => {
                        res.push(format!("pub mod {} {{\n", name));
                        let code: String = rec_result.to_owned();
                        res.push(code);
                        res.push(format!("}} // end of mod {}\n", name));
                    }
                }
            }
            res.join("")
        })
        .unwrap_or("// No modules".to_owned());

    vec![
        "// Automatically generated code\n".to_owned(),
        "#![allow(non_snake_case)]\n".to_owned(),
        modules_tree,
    ].join("\n") + "\n"
}
