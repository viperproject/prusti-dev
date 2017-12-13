use jni::JNIEnv;
use errors::*;
use gen_constructors::*;
use gen_methods::*;
use gen_object_getter::*;

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
