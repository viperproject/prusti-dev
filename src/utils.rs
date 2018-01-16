use std::ffi::CStr;
use jni::strings::JavaStr;
use errors::*;

pub fn get_return_signature(signature: &str) -> String {
    let splitted: Vec<&str> = signature.split(")").collect();
    splitted[1].to_string()
}

pub fn generate_jni_type(signature: &str) -> String {
    match signature.chars().nth(0).unwrap() {
        '[' => "JObject".to_string(),
        'L' => "JObject".to_string(),
        'B' => "jbyte".to_string(),
        'C' => "jchar".to_string(),
        'S' => "jshort".to_string(),
        'I' => "jint".to_string(),
        'J' => "jlong".to_string(),
        'Z' => "bool".to_string(),
        'F' => "jfloat".to_string(),
        'D' => "jdouble".to_string(),
        'V' => "()".to_string(),
        x => unreachable!(x),
    }
}

pub fn generate_return_jni_type(signature: &str) -> String {
    match signature.chars().nth(0).unwrap() {
        '[' => "JObject<'a>".to_string(),
        'L' => "JObject<'a>".to_string(),
        'B' => "jbyte".to_string(),
        'C' => "jchar".to_string(),
        'S' => "jshort".to_string(),
        'I' => "jint".to_string(),
        'J' => "jlong".to_string(),
        'Z' => "bool".to_string(),
        'F' => "jfloat".to_string(),
        'D' => "jdouble".to_string(),
        'V' => "()".to_string(),
        x => unreachable!(x),
    }
}

pub fn generate_jni_type_char(signature: &str) -> String {
    match signature.chars().nth(0).unwrap() {
        '[' => "l".to_string(),
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
        'Z' => format!("JValue::Bool({} as jboolean)", par),
        'F' => format!("JValue::Float({})", par),
        'D' => format!("JValue::Double({})", par),
        x => unreachable!(x),
    }
}

pub fn java_str_to_string(str: JavaStr) -> Result<String> {
    unsafe { Ok(CStr::from_ptr(str.get_raw()).to_str()?.to_string()) }
}

pub fn java_class_components(fqn: &str) -> Vec<String> {
    fqn.split("/")
        .map(|s| java_class_or_package_to_rust(s))
        .collect()
}

pub fn java_method_to_rust(method_name: &str) -> String {
    method_name.replace("_", "__").replace("$", "_dollar_")
    // If needed, replace other charachters with "_{something}_"
}

pub fn java_class_or_package_to_rust(class_name: &str) -> String {
    class_name.replace("$", "_object")
}
