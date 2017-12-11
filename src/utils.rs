use jni::strings::JavaStr;
use errors::*;
use std::ffi::CStr;
use heck::SnakeCase;

pub fn generate_code_header() -> String {
    "// Automatically generated code\n".into()
}

pub fn get_return_signature(signature: &str) -> String {
    let splitted: Vec<&str> = signature.split(")").collect();
    splitted[1].to_owned()
}

pub fn generate_jni_type(signature: &str) -> String {
    match signature.chars().nth(0).unwrap() {
        '[' => "JObject".to_owned(),
        'L' => "JObject".to_owned(),
        'B' => "jbyte".to_owned(),
        'C' => "jchar".to_owned(),
        'S' => "jshort".to_owned(),
        'I' => "jint".to_owned(),
        'J' => "jlong".to_owned(),
        'Z' => "jboolean".to_owned(),
        'F' => "jfloat".to_owned(),
        'D' => "jdouble".to_owned(),
        'V' => "()".to_owned(),
        x => unreachable!(x),
    }
}

pub fn generate_jni_type_char(signature: &str) -> String {
    match signature.chars().nth(0).unwrap() {
        '[' => "l".to_owned(),
        x => format!("{}", x.to_lowercase()),
    }
}

pub fn generate_jvalue_wrapper(par: &str, signature: &str) -> String {
    match signature.chars().nth(0).unwrap() {
        '[' => format!("JValue::Object({})", par),
        'L' => format!("JValue::Object({})", par),
        'B' => format!("JValue::Byte({})", par),
        'C' => format!("JValue::Char({})", par),
        'S' => format!("JValue::Short({})", par),
        'I' => format!("JValue::Int({})", par),
        'J' => format!("JValue::Long({})", par),
        'Z' => format!("JValue::Bool({})", par),
        'F' => format!("JValue::Float({})", par),
        'D' => format!("JValue::Double({})", par),
        x => unreachable!(x),
    }
}

pub fn java_str_to_string(str: JavaStr) -> Result<String> {
    unsafe { Ok(CStr::from_ptr(str.get_raw()).to_str()?.to_owned()) }
}

pub fn java_class_name_to_rust(name: &str) -> String {
    name.to_owned()
        .replace("$", "/object")
        .replace(".", "_")
        .replace("/", "_")
        .replace("__", "_")
        .to_snake_case()
}

pub fn java_name_to_rust(name: &str) -> String {
    name.to_owned()
        .replace("$", "_")
        .replace(".", "_")
        .replace("/", "_")
        .replace("__", "_")
        .to_snake_case()
}
