use jni::JNIEnv;
use jni::objects::JValue;
use errors::*;
use utils::*;

pub fn generate_all_constructors(env: &JNIEnv, target: &str) -> Result<String> {
    let mut generated_constructors = vec![];

    let clazz = env.find_class(target)?;

    let constructors = env.call_method(
        clazz.into(),
        "getConstructors",
        "()[Ljava/lang/reflect/Constructor;",
        &[],
    )?
        .l()?;
    let num_constructors = env.get_array_length(constructors.into_inner())?;

    for constructor_index in 0..num_constructors {
        let constructor = env.get_object_array_element(
            constructors.into_inner(),
            constructor_index,
        )?;

        let constructor_signature = java_str_to_string(env.get_string(
            env.call_static_method(
                "org.objectweb.asm.Type".replace(".", "/"),
                "getConstructorDescriptor",
                "(Ljava/lang/reflect/Constructor;)Ljava/lang/String;",
                &[JValue::Object(constructor)],
            )?
                .l()?
                .into(),
        )?)?;

        let mut parameter_names: Vec<String> = vec![];
        let mut parameter_signatures: Vec<String> = vec![];

        let parameters = env.call_method(
            constructor,
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

        let constructor_name = if constructor_index == 0 {
            "new".to_owned()
        } else {
            format!("new{}", constructor_index)
        };

        generated_constructors.push(generate_constructor(
            target,
            &constructor_name,
            &constructor_signature,
            &parameter_names,
            &parameter_signatures,
        ))

    }
    Ok(generated_constructors.join("\n"))
}

fn generate_constructor(
    target: &str,
    constructor_name: &str,
    constructor_signature: &str,
    parameter_names: &Vec<String>,
    parameter_signatures: &Vec<String>,
) -> String {
    assert_eq!(parameter_names.len(), parameter_signatures.len());

    let mut code: Vec<String> = vec![];
    code.push(format!(
        "/// Wrapped constructor of class {}",
        target.replace("/", ".")
    ));
    code.push("///".to_owned());
    code.push("/// Parameters:".to_owned());

    for i in 0..parameter_names.len() {
        let par_name = &parameter_names[i];
        let par_sign = &parameter_signatures[i];
        let par_type = generate_jni_type(&par_sign);
        code.push(format!("/// - {}: {} ({})", par_name, par_type, par_sign));
    }

    code.push(format!("pub fn {}<'a>(", constructor_name));
    code.push("    env: &'a JNIEnv,".to_owned());

    for i in 0..parameter_names.len() {
        let par_name = &parameter_names[i];
        let par_sign = &parameter_signatures[i];
        let par_type = generate_jni_type(&par_sign);
        code.push(format!("    {}: {},", par_name, par_type));
    }

    code.push(") -> Result<JObject<'a>> {".to_owned());
    code.push("    env.new_object(".to_owned());
    code.push(format!("        \"{}\",", target));
    code.push(format!("        \"{}\",", constructor_signature));
    code.push("        &[".to_owned());

    for i in 0..parameter_names.len() {
        let par_name = &parameter_names[i];
        let par_sign = &parameter_signatures[i];
        let par_jvalue = generate_jvalue_wrapper(&par_name, &par_sign);
        code.push(format!("            {},", par_jvalue));
    }

    code.push("        ]".to_owned());
    code.push("    )".to_owned());
    code.push("}".to_owned());

    code.join("\n") + "\n"
}
