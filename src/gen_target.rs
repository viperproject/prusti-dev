use jni::JNIEnv;
use errors::*;
use utils::*;
use gen_constructors::*;
use gen_methods::*;

pub fn generate_target_code(env: &JNIEnv, target: &str) -> Result<String> {
    Ok(
        vec![
            generate_code_header(),
            generate_opening_mod(target),
            generate_imports(),
            generate_scala_object_getter(target),
            generate_all_constructors(env, target)?,
            generate_all_methods(env, target)?,
            generate_closing_mod(target),
        ].join("\n"),
    )
}

fn mod_list(target: &str) -> Vec<String> {
    target
        .to_owned()
        .replace("$", "/object")
        .split("/")
        .map(|s| s.to_owned())
        .collect()
}

fn generate_opening_mod(target: &str) -> String {
    let mut code: Vec<String> = vec![];
    let names = mod_list(target);
    for name in &names {
        code.push(format!("pub mod {} {{", java_class_name_to_rust(name)));
    }
    code.join(" ") + "\n"
}

fn generate_imports() -> String {
    vec![
        "use jni::JNIEnv;",
        "use jni::objects::JObject;",
        "use jni::objects::JValue;",
        "use jni::errors::Result;",
        "use jni::sys::*;",
    ].join("\n") + "\n"
}

fn generate_closing_mod(target: &str) -> String {
    let mut code: Vec<String> = vec![];
    let names = mod_list(target);
    for _ in 0..names.len() {
        code.push("}".to_owned());
    }
    code.join(" ") + "\n"
}

fn generate_scala_object_getter(target: &str) -> String {
    let last_target_char: Vec<char> = target.chars().rev().take(1).collect();
    if last_target_char[0] != '$' {
        "".to_owned()
    } else {
        vec![
            "#[allow(dead_code)]".to_owned(),
            "pub fn get<'a>(env: &'a JNIEnv) -> Result<JObject<'a>> {".to_owned(),
            "    env.get_static_field(".to_owned(),
            format!("        \"{}\",", target),
            "        \"MODULE$\",".to_owned(),
            format!("        \"L{};\",", target),
            "    ).and_then(|x| x.l())".to_owned(),
            "}".to_owned(),
        ].join("\n") + "\n"
    }
}
