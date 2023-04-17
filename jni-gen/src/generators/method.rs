// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{class_name::*, errors::*, utils::*};
use jni::{
    objects::{JObject, JValue},
    JNIEnv,
};
use std::collections::BTreeMap;

pub fn generate_method(
    env: &JNIEnv,
    class: &ClassName,
    method_name: &str,
    target_signature: Option<String>,
    suffix: Option<String>,
) -> Result<String> {
    let MethodInfo {
        method_signature,
        method,
        is_static,
    } = find_method(env, class, method_name, target_signature)?;

    let parameters = env
        .call_method(
            method,
            "getParameters",
            "()[Ljava/lang/reflect/Parameter;",
            &[],
        )?
        .l()?;
    let num_parameters = env.get_array_length(*parameters)?;

    let mut parameter_names: Vec<String> = Vec::with_capacity(num_parameters as usize);
    let mut parameter_signatures: Vec<String> = Vec::with_capacity(num_parameters as usize);

    for parameter_index in 0..num_parameters {
        let parameter = env.get_object_array_element(*parameters, parameter_index)?;
        let parameter_name = env.get_string(
            env.call_method(parameter, "getName", "()Ljava/lang/String;", &[])?
                .l()?
                .into(),
        )?;
        let parameter_type = env
            .call_method(parameter, "getType", "()Ljava/lang/Class;", &[])?
            .l()?;
        let parameter_signature = env.get_string(
            env.call_static_method(
                "org/objectweb/asm/Type",
                "getDescriptor",
                "(Ljava/lang/Class;)Ljava/lang/String;",
                &[JValue::Object(parameter_type)],
            )?
            .l()?
            .into(),
        )?;

        parameter_names.push(java_str_to_valid_rust_argument_name(&parameter_name)?);
        parameter_signatures.push(java_str_to_string(&parameter_signature)?);
    }

    let rust_method_name = match suffix {
        None => format!("call_{}", java_identifier_to_rust(method_name)),
        Some(s) => format!("call_{}_{}", java_identifier_to_rust(method_name), s),
    };

    if is_static {
        Ok(generate_static(
            class,
            method_name,
            &rust_method_name,
            &method_signature,
            &parameter_names,
            &parameter_signatures,
        ))
    } else {
        Ok(generate(
            class,
            method_name,
            &rust_method_name,
            &method_signature,
            &parameter_names,
            &parameter_signatures,
        ))
    }
}

pub fn generate(
    class: &ClassName,
    method_name: &str,
    rust_method_name: &str,
    method_signature: &str,
    parameter_names: &[String],
    parameter_signatures: &[String],
) -> String {
    assert_eq!(parameter_names.len(), parameter_signatures.len());
    let return_signature = get_return_signature(method_signature);
    let return_type = generate_return_jni_type(&return_signature);

    let mut code: Vec<String> = vec![];
    code.push(format!(
        "/// Calls method `{}` of Java class `{}`.",
        method_name,
        class.full_name()
    ));

    if !parameter_names.is_empty() {
        code.push("///".to_string());
        code.push("/// Type and Java signature of parameters:".to_string());
        code.push("///".to_string());
    }

    for i in 0..parameter_names.len() {
        let par_name = &parameter_names[i];
        let par_sign = &parameter_signatures[i];
        let par_type = generate_jni_type(par_sign);
        code.push(format!("/// - `{par_name}`: `{par_type}` (`{par_sign}`)"));
    }

    code.push("///".to_string());
    code.push(format!(
        "/// Return type and Java signature: `{return_type}` (`{return_signature}`)"
    ));

    code.push(format!("pub fn {rust_method_name}("));
    code.push("    &self,".to_string());
    code.push("    receiver: JObject<'a>,".to_string());

    for i in 0..parameter_names.len() {
        let par_name = &parameter_names[i];
        let par_sign = &parameter_signatures[i];
        let par_type = generate_jni_type(par_sign);
        code.push(format!("    {par_name}: {par_type},"));
    }

    code.push(format!(") -> JNIResult<{return_type}> {{"));

    code.push(format!("    let class_name = \"{}\";", class.path()));
    code.push(format!("    let method_name = \"{method_name}\";"));
    code.push(format!(
        "    let method_signature = \"{method_signature}\";"
    ));

    for i in 0..parameter_names.len() {
        let par_name = &parameter_names[i];
        let par_sign = &parameter_signatures[i];
        if is_signature_of_class_type(par_sign) {
            let par_class = &par_sign[1..(par_sign.len() - 1)];
            code.push(format!("    let {par_name}_class_name = \"{par_class}\";"));
        }
    }

    code.push(format!(
        "    let return_signature = \"{return_signature}\";"
    ));
    if is_signature_of_class_type(&return_signature) {
        let return_class = &return_signature[1..(return_signature.len() - 1)];
        code.push(format!("    let return_class_name = \"{return_class}\";"))
    }
    code.push("".to_string());

    // Generate dynamic type check for the arguments
    for i in 0..parameter_names.len() {
        let par_name = &parameter_names[i];
        let par_sign = &parameter_signatures[i];
        if is_signature_of_class_type(par_sign) {
            code.push(generate_variable_type_check(
                par_name,
                &format!("{par_name}_class_name"),
            ));
        }
    }

    // Generate dynamic type check for `receiver`
    code.push(generate_variable_type_check("receiver", "class_name"));

    code.push(
        r#"    static METHOD_ID: OnceCell<JMethodID> = OnceCell::new();
    static RETURN_TYPE: OnceCell<ReturnType> = OnceCell::new();
    let method_id = *METHOD_ID.get_or_try_init(|| {
        self.env.get_method_id(
            class_name,
            method_name,
            method_signature
        )
    })?;
    let return_type = RETURN_TYPE.get_or_try_init(|| {
        ReturnType::from_str(return_signature)
    })?.clone();
"#
        .to_string(),
    );

    code.push("    let result = self.env.call_method_unchecked(".to_string());
    code.push("        receiver,".to_string());
    code.push("        method_id,".to_string());
    code.push("        return_type,".to_string());
    code.push("        &[".to_string());

    for i in 0..parameter_names.len() {
        let par_name = &parameter_names[i];
        let par_sign = &parameter_signatures[i];
        let par_jvalue = generate_jvalue_wrapper(par_name, par_sign);
        code.push(format!("            {par_jvalue}.into(),"));
    }

    code.push("        ]".to_string());
    code.push(format!(
        "    ).and_then(|x| x.{}());",
        generate_jni_type_char(&return_signature)
    ));
    code.push("".to_string());

    // Generate dynamic type check for the result
    if is_signature_of_class_type(&return_signature) {
        code.push(generate_result_type_check("return_class_name"));
    }

    code.push("    result".to_string());
    code.push("}".to_string());

    code.join("\n") + "\n"
}

fn generate_static(
    class: &ClassName,
    method_name: &str,
    rust_method_name: &str,
    method_signature: &str,
    parameter_names: &[String],
    parameter_signatures: &[String],
) -> String {
    assert_eq!(parameter_names.len(), parameter_signatures.len());
    let return_signature = get_return_signature(method_signature);
    let return_type = generate_return_jni_type(&return_signature);

    let mut code: Vec<String> = vec![];
    code.push(format!(
        "/// Calls static method `{}` of Java class `{}`.",
        method_name,
        class.full_name()
    ));
    code.push("///".to_string());
    code.push("/// Type and Java signature of parameters:".to_string());
    code.push("///".to_string());

    for i in 0..parameter_names.len() {
        let par_name = &parameter_names[i];
        let par_sign = &parameter_signatures[i];
        let par_type = generate_jni_type(par_sign);
        code.push(format!("/// - `{par_name}`: `{par_type}` (`{par_sign}`)"));
    }

    code.push("///".to_string());
    code.push(format!(
        "/// Return type and Java signature: `{return_type}` (`{return_signature}`)"
    ));

    code.push(format!("pub fn {rust_method_name}("));
    code.push("    &self,".to_string());

    for i in 0..parameter_names.len() {
        let par_name = &parameter_names[i];
        let par_sign = &parameter_signatures[i];
        let par_type = generate_jni_type(par_sign);
        code.push(format!("    {par_name}: {par_type},"));
    }

    code.push(format!(") -> JNIResult<{return_type}> {{"));

    code.push(format!("    let class_name = \"{}\";", class.path()));
    code.push(format!("    let method_name = \"{method_name}\";"));
    code.push(format!(
        "    let method_signature = \"{method_signature}\";"
    ));

    for i in 0..parameter_names.len() {
        let par_name = &parameter_names[i];
        let par_sign = &parameter_signatures[i];
        if is_signature_of_class_type(par_sign) {
            let par_class = &par_sign[1..(par_sign.len() - 1)];
            code.push(format!("    let {par_name}_class_name = \"{par_class}\";"));
        }
    }

    code.push(format!(
        "    let return_signature = \"{return_signature}\";"
    ));
    if is_signature_of_class_type(&return_signature) {
        let return_class = &return_signature[1..(return_signature.len() - 1)];
        code.push(format!("    let return_class_name = \"{return_class}\";"))
    }
    code.push("".to_string());

    // Generate dynamic type check for the arguments
    for i in 0..parameter_names.len() {
        let par_name = &parameter_names[i];
        let par_sign = &parameter_signatures[i];
        if is_signature_of_class_type(par_sign) {
            code.push(generate_variable_type_check(
                par_name,
                &format!("{par_name}_class_name"),
            ));
        }
    }

    code.push(
        r#"    static CLASS: OnceCell<GlobalRef> = OnceCell::new();
    static STATIC_METHOD_ID: OnceCell<JStaticMethodID> = OnceCell::new();
    static RETURN_TYPE: OnceCell<ReturnType> = OnceCell::new();
    let class = CLASS.get_or_try_init(|| {
        let class = self.env.find_class(class_name)?;
        self.env.new_global_ref(class)
    })?;
    let static_method_id = *STATIC_METHOD_ID.get_or_try_init(|| {
        self.env.get_static_method_id(
            class_name,
            method_name,
            method_signature
        )
    })?;
    let return_type = RETURN_TYPE.get_or_try_init(|| {
        ReturnType::from_str(return_signature)
    })?.clone();
"#
        .to_string(),
    );

    code.push("    let result = self.env.call_static_method_unchecked(".to_string());
    code.push("        JClass::from(class.as_obj()),".to_string());
    code.push("        static_method_id,".to_string());
    code.push("        return_type,".to_string());
    code.push("        &[".to_string());
    for i in 0..parameter_names.len() {
        let par_name = &parameter_names[i];
        let par_sign = &parameter_signatures[i];
        let par_jvalue = generate_jvalue_wrapper(par_name, par_sign);
        code.push(format!("            {par_jvalue}.into(),"));
    }
    code.push("        ]".to_string());
    code.push(format!(
        "    ).and_then(|x| x.{}());",
        generate_jni_type_char(&return_signature)
    ));
    code.push("".to_string());

    // Generate dynamic type check for the result
    // Generate dynamic type check for the result
    if is_signature_of_class_type(&return_signature) {
        code.push(generate_result_type_check("return_class_name"));
    }

    code.push("    result".to_string());
    code.push("}".to_string());

    code.join("\n") + "\n"
}

pub struct MethodInfo<'a> {
    pub method_signature: String,
    pub method: JObject<'a>,
    pub is_static: bool,
}

pub fn find_method<'a>(
    env: &'a JNIEnv<'a>,
    class: &'a ClassName,
    method_name: &'a str,
    target_signature: Option<String>,
) -> Result<MethodInfo<'a>> {
    let clazz = env.find_class(class.path())?;

    let methods = env
        .call_method(clazz, "getMethods", "()[Ljava/lang/reflect/Method;", &[])?
        .l()?;
    let num_methods = env.get_array_length(*methods)?;

    let mut indexed_methods = BTreeMap::new();

    for method_index in 0..num_methods {
        let method = env.get_object_array_element(*methods, method_index)?;

        let method_name = java_str_to_string(
            &env.get_string(
                env.call_method(method, "getName", "()Ljava/lang/String;", &[])?
                    .l()?
                    .into(),
            )?,
        )?;

        let method_signature = java_str_to_string(
            &env.get_string(
                env.call_static_method(
                    "org/objectweb/asm/Type",
                    "getMethodDescriptor",
                    "(Ljava/lang/reflect/Method;)Ljava/lang/String;",
                    &[JValue::Object(method)],
                )?
                .l()?
                .into(),
            )?,
        )?;

        match indexed_methods.remove(&method_name) {
            None => {
                let mut signature_map = BTreeMap::new();
                signature_map.insert(method_signature, method);
                indexed_methods.insert(method_name, signature_map);
            }
            Some(mut signature_map) => {
                signature_map.insert(method_signature, method);
                indexed_methods.insert(method_name, signature_map);
            }
        }
    }

    let matching_methods = match indexed_methods.get_mut(method_name) {
        None => return Err(ErrorKind::NoMethod(class.full_name(), method_name.into()).into()),
        Some(mm) => mm,
    };

    let (method_signature, method): (String, JObject) = match target_signature {
        None => {
            if matching_methods.is_empty() {
                unreachable!();
            }
            if matching_methods.len() > 1 {
                return Err(ErrorKind::AmbiguousMethod(
                    class.full_name(),
                    method_name.into(),
                    matching_methods.keys().map(|k| k.to_string()).collect(),
                )
                .into());
            }
            matching_methods.pop_first().unwrap()
        }
        Some(sign) => match matching_methods.get(&sign) {
            Some(constr) => (sign, *constr),
            None => {
                return Err(ErrorKind::NoMatchingMethod(
                    class.full_name(),
                    method_name.into(),
                    sign,
                )
                .into())
            }
        },
    };

    let method_modifier = env.call_method(method, "getModifiers", "()I", &[])?.i()?;

    let is_static = env
        .call_static_method(
            "java/lang/reflect/Modifier",
            "isStatic",
            "(I)Z",
            &[JValue::Int(method_modifier)],
        )?
        .z()?;

    Ok(MethodInfo {
        method_signature,
        method,
        is_static,
    })
}
