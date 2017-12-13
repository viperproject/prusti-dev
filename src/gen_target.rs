use jni::JNIEnv;
use errors::*;
use gen_constructors::*;
use gen_methods::*;

pub fn generate_target_code(env: &JNIEnv, target: &str) -> Result<String> {
    Ok(
        vec![
            format!("//! Automatically generated code for '{}'\n", target),
            "#![allow(non_snake_case)]\n".to_owned(),
            generate_imports(),
            generate_scala_object_getter(target),
            generate_all_constructors(env, target)?,
            generate_all_methods(env, target)?,
        ].join("\n"),
    )
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

fn generate_scala_object_getter(target: &str) -> String {
    let last_target_char: Vec<char> = target.chars().rev().take(1).collect();
    if last_target_char[0] != '$' {
        "".to_owned()
    } else {
        vec![
            format!(
                "/// Wrapped getter of Scala object {}",
                target.replace("/", ".")
            ),
            "#[allow(dead_code)]".to_owned(),
            "pub fn new<'a>(env: &'a JNIEnv) -> Result<JObject<'a>> {".to_owned(),
            "    env.get_static_field(".to_owned(),
            format!("        \"{}\",", target),
            "        \"MODULE$\",".to_owned(),
            format!("        \"L{};\",", target),
            "    ).and_then(|x| x.l())".to_owned(),
            "}".to_owned(),
        ].join("\n") + "\n"
    }
}
