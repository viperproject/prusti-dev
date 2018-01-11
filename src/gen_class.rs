use jni::JNIEnv;
use errors::*;
use gen_constructors::*;
use gen_methods::*;
use gen_object_getter::*;
use utils::java_class_components;

pub fn generate_class_code(env: &JNIEnv, class: &str) -> Result<String> {
    Ok(
        vec![
            format!("//! Automatically generated code for '{}'\n", class),
            "#![allow(non_snake_case)]\n".to_owned(),
            "#![allow(unused_imports)]\n".to_owned(),
            generate_imports(),
            generate_struct(class),
            generate_begin_impl(class),
            generate_scala_object_getter(class),
            generate_all_constructors(env, class)?,
            generate_all_methods(env, class)?,
            generate_end_impl(class),
        ].join("\n"),
    )
}

fn generate_imports() -> String {
    vec![
        "use jni::JNIEnv;",
        "use jni::objects::JObject;",
        "use jni::objects::JValue;",
        "use jni::errors::Result as JNIResult;",
        "use jni::sys::*;",
        "use jni::signature::*;",
    ].join("\n") + "\n"
}

fn generate_struct(class: &str) -> String {
    let class_name = java_class_components(class).last().unwrap().to_owned();
    vec![
        "#[allow(non_camel_case_types)]".to_owned(),
        format!("pub struct {}<'a> {{", class_name),
        "    env: &'a JNIEnv<'a>,".to_owned(),
        "}".to_owned(),
    ].join("\n") + "\n"
}

fn generate_begin_impl(class: &str) -> String {
    let class_name = java_class_components(class).last().unwrap().to_owned();
    vec![
        format!("impl<'a> {}<'a> {{", class_name),
        "".to_owned(),
        "pub fn with(env: &'a JNIEnv<'a>) -> Self {".to_owned(),
        format!("    {}{{ env: env }}", class_name),
        "}".to_owned(),
    ].join("\n") + "\n"
}

fn generate_end_impl(class: &str) -> String {
    let class_name = java_class_components(class).last().unwrap().to_owned();
    format!("}} // end of impl {}\n", class_name)
}
