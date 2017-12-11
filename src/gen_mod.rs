use utils::*;

pub fn generate_target_mod_code(targets: &Vec<String>) -> String {
    let mut code: Vec<String> = vec![];

    code.push(generate_code_header());

    for target in targets {
        let target_filename = java_class_name_to_rust(&target);
        code.push(format!("mod {};", target_filename));
        code.push(format!("pub use self::{}::*;", target_filename));
    }

    code.join("\n")
}
