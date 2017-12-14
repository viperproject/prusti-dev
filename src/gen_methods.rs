use std::collections::HashMap;
use std::collections::BTreeMap;
use jni::JNIEnv;
use jni::objects::JValue;
use errors::*;
use utils::*;

pub fn generate_all_methods(env: &JNIEnv, class: &str) -> Result<String> {
    let mut generated_methods = vec![];
    let mut used_method_counter = HashMap::new();

    let clazz = env.find_class(class)?;

    let methods = env.call_method(
        clazz.into(),
        "getMethods",
        "()[Ljava/lang/reflect/Method;",
        &[],
    )?
        .l()?;
    let num_methods = env.get_array_length(methods.into_inner())?;

    let mut sorted_methods = BTreeMap::new();

    for method_index in 0..num_methods {
        let method = env.get_object_array_element(
            methods.into_inner(),
            method_index,
        )?;

        let method_name = java_str_to_string(env.get_string(
            env.call_method(
                method,
                "getName",
                "()Ljava/lang/String;",
                &[],
            )?
                .l()?
                .into(),
        )?)?;

        let method_signature = java_str_to_string(env.get_string(
            env.call_static_method(
                "org.objectweb.asm.Type".replace(".", "/"),
                "getMethodDescriptor",
                "(Ljava/lang/reflect/Method;)Ljava/lang/String;",
                &[JValue::Object(method)],
            )?
                .l()?
                .into(),
        )?)?;

        sorted_methods.insert((method_name, method_signature), method);
    }

    // Iterate on the ordered list of methods
    for (&(ref method_name, ref method_signature), method) in sorted_methods.iter() {
        let method_modifier = env.call_method(*method, "getModifiers", "()I", &[])?.i()?;

        let is_static = env.call_static_method(
            "java.lang.reflect.Modifier".replace(".", "/"),
            "isStatic",
            "(I)Z",
            &[JValue::Int(method_modifier)],
        )?
            .z()?;

        let mut parameter_names: Vec<String> = vec![];
        let mut parameter_signatures: Vec<String> = vec![];

        let parameters = env.call_method(
            *method,
            "getParameters",
            "()[Ljava/lang/reflect/Parameter;",
            &[],
        )?
            .l()?;
        let num_parameters = env.get_array_length(parameters.into_inner())?;

        for parameter_index in 0..num_parameters {
            let parameter = env.get_object_array_element(
                parameters.into_inner(),
                parameter_index,
            )?;
            let parameter_name = env.get_string(
                env.call_method(
                    parameter,
                    "getName",
                    "()Ljava/lang/String;",
                    &[],
                )?
                    .l()?
                    .into(),
            )?;
            let parameter_type = env.call_method(parameter, "getType", "()Ljava/lang/Class;", &[])?
                .l()?;
            let parameter_signature = env.get_string(
                env.call_static_method(
                    "org.objectweb.asm.Type".replace(".", "/"),
                    "getDescriptor",
                    "(Ljava/lang/Class;)Ljava/lang/String;",
                    &[JValue::Object(parameter_type)],
                )?
                    .l()?
                    .into(),
            )?;

            parameter_names.push(java_str_to_string(parameter_name)?);
            parameter_signatures.push(java_str_to_string(parameter_signature)?);
        }

        let counter = match used_method_counter.get(method_name) {
            None => 0,
            Some(x) => *x,
        };
        let unique_method_name = if counter == 0 {
            format!("call_{}", method_name)
        } else {
            format!("call_{}_{}", method_name, counter)
        };
        used_method_counter.insert(method_name.clone(), counter + 1);

        if is_static {
            generated_methods.push(generate_static_method(
                class,
                method_name,
                &unique_method_name,
                &method_signature,
                &parameter_names,
                &parameter_signatures,
            ));
        } else {
            generated_methods.push(generate_method(
                class,
                method_name,
                &unique_method_name,
                &method_signature,
                &parameter_names,
                &parameter_signatures,
            ));
        }
    }

    Ok(generated_methods.join("\n"))
}


fn generate_method(
    class: &str,
    method_name: &str,
    unique_method_name: &str,
    method_signature: &str,
    parameter_names: &Vec<String>,
    parameter_signatures: &Vec<String>,
) -> String {
    assert_eq!(parameter_names.len(), parameter_signatures.len());
    let return_signature = get_return_signature(method_signature);
    let return_type = generate_return_jni_type(&return_signature);

    let mut code: Vec<String> = vec![];
    code.push(format!(
        "/// Calls method `{}` of Java class `{}`.",
        method_name,
        class.replace("/", ".")
    ));
    code.push("///".to_owned());
    code.push("/// Type and Java signature of parameters:".to_owned());
    code.push("///".to_owned());

    for i in 0..parameter_names.len() {
        let par_name = &parameter_names[i];
        let par_sign = &parameter_signatures[i];
        let par_type = generate_jni_type(&par_sign);
        code.push(format!(
            "/// - `{}`: `{}` (`{}`)",
            par_name,
            par_type,
            par_sign
        ));
    }

    code.push("///".to_owned());
    code.push(format!(
        "/// Return type and Java signature: `{}` (`{}`)",
        return_type,
        return_signature
    ));

    code.push("#[allow(dead_code)]".to_owned());
    code.push(format!(
        "pub fn {}(",
        java_method_to_rust(unique_method_name)
    ));
    code.push("    &self,".to_owned());
    code.push("    receiver: JObject,".to_owned());

    for i in 0..parameter_names.len() {
        let par_name = &parameter_names[i];
        let par_sign = &parameter_signatures[i];
        let par_type = generate_jni_type(&par_sign);
        code.push(format!("    {}: {},", par_name, par_type));
    }

    code.push(format!(") -> Result<{}> {{", return_type));
    code.push("    self.env.call_method(".to_owned());
    code.push("        receiver,".to_owned());
    code.push(format!("        \"{}\",", method_name));
    code.push(format!("        \"{}\",", method_signature));
    code.push("        &[".to_owned());

    for i in 0..parameter_names.len() {
        let par_name = &parameter_names[i];
        let par_sign = &parameter_signatures[i];
        let par_jvalue = generate_jvalue_wrapper(&par_name, &par_sign);
        code.push(format!("            {},", par_jvalue));
    }

    code.push("        ]".to_owned());
    code.push(format!(
        "    ).and_then(|x| x.{}())",
        generate_jni_type_char(&return_signature)
    ));
    code.push("}".to_owned());

    code.join("\n") + "\n"
}

fn generate_static_method(
    class: &str,
    method_name: &str,
    unique_method_name: &str,
    method_signature: &str,
    parameter_names: &Vec<String>,
    parameter_signatures: &Vec<String>,
) -> String {
    assert_eq!(parameter_names.len(), parameter_signatures.len());
    let return_signature = get_return_signature(method_signature);
    let return_type = generate_return_jni_type(&return_signature);

    let mut code: Vec<String> = vec![];
    code.push(format!(
        "/// Calls static method `{}` of Java class `{}`.",
        method_name,
        class.replace("/", ".")
    ));
    code.push("///".to_owned());
    code.push("/// Type and Java signature of parameters:".to_owned());
    code.push("///".to_owned());

    for i in 0..parameter_names.len() {
        let par_name = &parameter_names[i];
        let par_sign = &parameter_signatures[i];
        let par_type = generate_jni_type(&par_sign);
        code.push(format!(
            "/// - `{}`: `{}` (`{}`)",
            par_name,
            par_type,
            par_sign
        ));
    }

    code.push("///".to_owned());
    code.push(format!(
        "/// Return type and Java signature: `{}` (`{}`)",
        return_type,
        return_signature
    ));

    code.push("#[allow(dead_code)]".to_owned());
    code.push(format!(
        "pub fn {}(",
        java_method_to_rust(unique_method_name)
    ));
    code.push("    &self,".to_owned());

    for i in 0..parameter_names.len() {
        let par_name = &parameter_names[i];
        let par_sign = &parameter_signatures[i];
        let par_type = generate_jni_type(&par_sign);
        code.push(format!("    {}: {},", par_name, par_type));
    }

    code.push(format!(") -> Result<{}> {{", return_type));
    code.push("    self.env.call_static_method(".to_owned());
    code.push(format!("        \"{}\",", class));
    code.push(format!("        \"{}\",", method_name));
    code.push(format!("        \"{}\",", method_signature));
    code.push("        &[".to_owned());

    for i in 0..parameter_names.len() {
        let par_name = &parameter_names[i];
        let par_sign = &parameter_signatures[i];
        let par_jvalue = generate_jvalue_wrapper(&par_name, &par_sign);
        code.push(format!("            {},", par_jvalue));
    }

    code.push("        ]".to_owned());
    code.push(format!(
        "    ).and_then(|x| x.{}())",
        generate_jni_type_char(&return_signature)
    ));
    code.push("}".to_owned());

    code.join("\n") + "\n"
}
