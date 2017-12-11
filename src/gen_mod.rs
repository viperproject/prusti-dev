use jni::JNIEnv;
use errors::*;
use utils::*;
use gen_constructors::*;
use gen_methods::*;

pub fn generate_target_mod_code(env: &JNIEnv, targets: &Vec<String>) -> String {
    let mut code: Vec<String> = vec![];

    code.push(generate_code_header());

    for target in targets {
        let target_filename = java_name_to_rust(&target);
        code.push(format!("mod {};", target_filename));
        code.push(format!("pub use {}::*;", target_filename));
    }

    code.join("\n")
}
