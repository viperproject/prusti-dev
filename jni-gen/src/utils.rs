// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::errors::*;
use jni::strings::JavaStr;
use std::ffi::CStr;

pub fn get_return_signature(signature: &str) -> String {
    let splitted: Vec<&str> = signature.split(')').collect();
    splitted[1].to_string()
}

pub fn generate_jni_type(signature: &str) -> String {
    match signature.chars().next().unwrap() {
        '[' | 'L' => "JObject".to_string(),
        'B' => "jbyte".to_string(),
        'C' => "jchar".to_string(),
        'S' => "jshort".to_string(),
        'I' => "jint".to_string(),
        'J' => "jlong".to_string(),
        'Z' => "bool".to_string(),
        'F' => "jfloat".to_string(),
        'D' => "jdouble".to_string(),
        'V' => "()".to_string(),
        x => unreachable!("{}", x),
    }
}

pub fn generate_return_jni_type(signature: &str) -> String {
    match signature.chars().next().unwrap() {
        '[' | 'L' => "JObject<'a>".to_string(),
        'B' => "jbyte".to_string(),
        'C' => "jchar".to_string(),
        'S' => "jshort".to_string(),
        'I' => "jint".to_string(),
        'J' => "jlong".to_string(),
        'Z' => "bool".to_string(),
        'F' => "jfloat".to_string(),
        'D' => "jdouble".to_string(),
        'V' => "()".to_string(),
        x => unreachable!("{}", x),
    }
}

pub fn generate_jni_type_char(signature: &str) -> String {
    match signature.chars().next().unwrap() {
        '[' => "l".to_string(),
        x => x.to_lowercase().to_string(),
    }
}

pub fn generate_jvalue_wrapper(par: &str, signature: &str) -> String {
    match signature.chars().next().unwrap() {
        '[' | 'L' => format!("JValue::Object({par})"),
        'B' => format!("JValue::Byte({par})"),
        'C' => format!("JValue::Char({par})"),
        'S' => format!("JValue::Short({par})"),
        'I' => format!("JValue::Int({par})"),
        'J' => format!("JValue::Long({par})"),
        'Z' => format!("JValue::Bool({par} as jboolean)"),
        'F' => format!("JValue::Float({par})"),
        'D' => format!("JValue::Double({par})"),
        x => unreachable!("{}", x),
    }
}

pub fn java_str_to_string(string: &JavaStr) -> Result<String> {
    unsafe { Ok(CStr::from_ptr(string.get_raw()).to_str()?.to_string()) }
}

pub fn java_str_to_valid_rust_argument_name(string: &JavaStr) -> Result<String> {
    Ok(format!(
        "arg_{}",
        java_identifier_to_rust(&java_str_to_string(string)?)
    ))
}

pub fn java_identifier_to_rust(name: &str) -> String {
    // identifier can only be composed of [a-zA-Z&_] characters - https://docs.oracle.com/javase/specs/jls/se7/html/jls-3.html#jls-3.8
    name.replace('_', "__").replace('$', "_dollar_")
}

// Runtime checks for objects are performed only on variables of class types. Those have signature starting with 'L'.
pub fn is_signature_of_class_type(signature: &str) -> bool {
    signature.starts_with('L')
}

/// Generates a runtime check that the object is of the expected class - applies only to object types (starting with L)
/// If this value is also the returned value (result), unwrap it first (since it is of type Result<T>)
fn generate_type_check(variable_name: &str, variable_type_name: &str, is_result: bool) -> String {
    let mut type_check: Vec<String> = vec![];
    type_check.push("    debug_assert!(".to_string());
    type_check.push(format!(
        "        self.env.is_instance_of({variable_name}, self.env.find_class({variable_type_name})?)?"
    ));
    type_check.push("    );".to_string());

    if is_result {
        let indented_type_check = type_check
            .iter()
            .map(|x| format!("    {x}"))
            .collect::<Vec<_>>()
            .join("\n");

        vec![
            "    if let Ok(result) = result {".to_string(),
            indented_type_check,
            "    }".to_string(),
        ]
    } else {
        type_check
    }
    .join("\n")
        + "\n"
}

/// Generates dynamic type checks to assert that the result (named result and wrapped in the Result enum) object is of an expected class.
/// Only to be called on object of java class types (having signature starting with L)
/// class_name_variable_name - needs to be a name of a variable in the generated code that holds the '/'-separated class name
pub fn generate_result_type_check(class_name_variable_name: &str) -> String {
    generate_type_check("result", class_name_variable_name, true)
}

/// Generates dynamic type checks to assert that an object (receiver or parameter) is of an expected class.
/// Only to be called on object of java class types (having signature starting with L)
/// class_name_variable_name - needs to be a name of a variable in the generated code that holds the '/'-separated class name
pub fn generate_variable_type_check(variable_name: &str, class_name_variable_name: &str) -> String {
    generate_type_check(variable_name, class_name_variable_name, false)
}

// pub fn generate_method(
//     env: &JNIEnv,
//     class: &ClassName,
//     method_name: &str,
//     target_signature: Option<String>,
//     suffix: Option<String>,
// ) -> Result<String> {
//     let clazz = env.find_class(class.path())?;

//     let methods = env
//         .call_method(clazz, "getMethods", "()[Ljava/lang/reflect/Method;", &[])?
//         .l()?;
//     let num_methods = env.get_array_length(*methods)?;

//     let mut indexed_methods = BTreeMap::new();

//     for method_index in 0..num_methods {
//         let method = env.get_object_array_element(*methods, method_index)?;

//         let method_name = java_str_to_string(
//             &env.get_string(
//                 env.call_method(method, "getName", "()Ljava/lang/String;", &[])?
//                     .l()?
//                     .into(),
//             )?,
//         )?;

//         let method_signature = java_str_to_string(
//             &env.get_string(
//                 env.call_static_method(
//                     "org/objectweb/asm/Type",
//                     "getMethodDescriptor",
//                     "(Ljava/lang/reflect/Method;)Ljava/lang/String;",
//                     &[JValue::Object(method)],
//                 )?
//                 .l()?
//                 .into(),
//             )?,
//         )?;

//         match indexed_methods.remove(&method_name) {
//             None => {
//                 let mut signature_map = BTreeMap::new();
//                 signature_map.insert(method_signature, method);
//                 indexed_methods.insert(method_name, signature_map);
//             }
//             Some(mut signature_map) => {
//                 signature_map.insert(method_signature, method);
//                 indexed_methods.insert(method_name, signature_map);
//             }
//         }
//     }

//     let matching_methods = match indexed_methods.get_mut(method_name) {
//         None => return Err(ErrorKind::NoMethod(class.full_name(), method_name.into()).into()),
//         Some(mm) => mm,
//     };

//     let (method_signature, method): (String, JObject) = match target_signature {
//         None => {
//             if matching_methods.is_empty() {
//                 unreachable!();
//             }
//             if matching_methods.len() > 1 {
//                 return Err(ErrorKind::AmbiguousMethod(
//                     class.full_name(),
//                     method_name.into(),
//                     matching_methods.keys().map(|k| k.to_string()).collect(),
//                 )
//                 .into());
//             }
//             matching_methods.pop_first().unwrap()
//         }
//         Some(sign) => match matching_methods.get(&sign) {
//             Some(constr) => (sign, *constr),
//             None => {
//                 return Err(ErrorKind::NoMatchingMethod(
//                     class.full_name(),
//                     method_name.into(),
//                     sign,
//                 )
//                 .into())
//             }
//         },
//     };

//     let method_modifier = env.call_method(method, "getModifiers", "()I", &[])?.i()?;

//     let is_static = env
//         .call_static_method(
//             "java/lang/reflect/Modifier",
//             "isStatic",
//             "(I)Z",
//             &[JValue::Int(method_modifier)],
//         )?
//         .z()?;

//     let parameters = env
//         .call_method(
//             method,
//             "getParameters",
//             "()[Ljava/lang/reflect/Parameter;",
//             &[],
//         )?
//         .l()?;
//     let num_parameters = env.get_array_length(*parameters)?;

//     let mut parameter_names: Vec<String> = Vec::with_capacity(num_parameters as usize);
//     let mut parameter_signatures: Vec<String> = Vec::with_capacity(num_parameters as usize);

//     for parameter_index in 0..num_parameters {
//         let parameter = env.get_object_array_element(*parameters, parameter_index)?;
//         let parameter_name = env.get_string(
//             env.call_method(parameter, "getName", "()Ljava/lang/String;", &[])?
//                 .l()?
//                 .into(),
//         )?;
//         let parameter_type = env
//             .call_method(parameter, "getType", "()Ljava/lang/Class;", &[])?
//             .l()?;
//         let parameter_signature = env.get_string(
//             env.call_static_method(
//                 "org/objectweb/asm/Type",
//                 "getDescriptor",
//                 "(Ljava/lang/Class;)Ljava/lang/String;",
//                 &[JValue::Object(parameter_type)],
//             )?
//             .l()?
//             .into(),
//         )?;

//         parameter_names.push(java_str_to_valid_rust_argument_name(&parameter_name)?);
//         parameter_signatures.push(java_str_to_string(&parameter_signature)?);
//     }

//     let rust_method_name = match suffix {
//         None => format!("call_{}", java_identifier_to_rust(method_name)),
//         Some(s) => format!("call_{}_{}", java_identifier_to_rust(method_name), s),
//     };

//     if is_static {
//         Ok(generate_static(
//             class,
//             method_name,
//             &rust_method_name,
//             &method_signature,
//             &parameter_names,
//             &parameter_signatures,
//         ))
//     } else {
//         Ok(generate(
//             class,
//             method_name,
//             &rust_method_name,
//             &method_signature,
//             &parameter_names,
//             &parameter_signatures,
//         ))
//     }
// }