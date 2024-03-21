// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{class_name::*, errors::*, utils::*};
use jni::{
    objects::{JClass, JObject, JValue},
    JNIEnv,
};

use super::trait_field_getter_setter;

fn hierarchy_field_lookup<'a>(
    env: &JNIEnv<'a>,
    class: &ClassName,
    lookup_name: &str,
) -> Result<Option<JObject<'a>>> {
    let mut class = env.find_class(class.path())?;
    while !class.is_null() {
        if let Some(field) = class_field_lookup(env, class, lookup_name)? {
            return Ok(Some(field));
        }

        class = env.get_superclass(class)?;
    }

    Ok(None)
}

fn class_field_lookup<'a>(
    env: &JNIEnv<'a>,
    class: JClass<'a>,
    lookup_name: &str,
) -> Result<Option<JObject<'a>>> {
    let fields = env
        .call_method(
            class,
            "getDeclaredFields",
            "()[Ljava/lang/reflect/Field;",
            &[],
        )?
        .l()?;

    let num_fields = env.get_array_length(*fields)?;

    for field_index in 0..num_fields {
        let field = env.get_object_array_element(*fields, field_index)?;

        let field_name = java_str_to_string(
            &env.get_string(
                env.call_method(field, "getName", "()Ljava/lang/String;", &[])?
                    .l()?
                    .into(),
            )?,
        )?;

        if field_name == lookup_name {
            return Ok(Some(field));
        }
    }

    Ok(None)
}

fn generate_field_getter(class: &ClassName, field_name: &str, type_signature: &str) -> String {
    let rust_getter_name = format!("get_{}", java_identifier_to_rust(field_name));
    let parameter_type = generate_jni_type(type_signature);

    let mut code: Vec<String> = vec![];
    code.push(format!(
        "/// Returns the field `{}` of the scala class `{}`.",
        field_name,
        class.full_name()
    ));
    code.push("///".to_string());
    code.push(format!(
        "/// Return type and Java signature: `{parameter_type}` (`{type_signature}`)"
    ));
    code.push(format!("pub fn {rust_getter_name}("));
    code.push("    &self,".to_string());
    code.push("    receiver: JObject<'a>,".to_string());
    code.push(format!(") -> JNIResult<{parameter_type}> {{"));
    code.push(format!("    let class_name = \"{}\";", class.path()));
    code.push(format!("    let field_name = \"{field_name}\";"));
    code.push(format!("    let return_signature = \"{type_signature}\";"));
    if is_signature_of_class_type(type_signature) {
        let type_class = &type_signature[1..(type_signature.len() - 1)];
        code.push(format!("    let return_class_name = \"{type_class}\";"))
    }
    code.push("".to_string());
    code.push(generate_variable_type_check("receiver", "class_name"));
    code.push("    let result = self.env.get_field(".to_string());
    code.push("        receiver,".to_string());
    code.push("        field_name,".to_string());
    code.push("        return_signature,".to_string());
    code.push(format!(
        "    ).and_then(|x| x.{}());",
        generate_jni_type_char(type_signature)
    ));
    code.push("".to_string());
    if is_signature_of_class_type(type_signature) {
        code.push(generate_result_type_check("return_class_name"));
    }

    code.push("    result".to_string());
    code.push("}".to_string());

    code.join("\n") + "\n"
}

fn generate_field_setter(class: &ClassName, field_name: &str, type_signature: &str) -> String {
    let rust_setter_name = format!("set_{}", java_identifier_to_rust(field_name));
    let parameter_name = format!("new_{field_name}");
    let parameter_type = generate_jni_type(type_signature);

    let mut code: Vec<String> = vec![];
    code.push(format!(
        "/// Sets the field `{}` of the scala class `{}`.",
        field_name,
        class.full_name()
    ));
    code.push("///".to_string());
    code.push("/// Type and Java signature of parameters:".to_string());
    code.push("///".to_string());
    code.push(format!(
        "/// - `{parameter_name}`: `{parameter_type}` (`{type_signature}`)"
    ));
    code.push("/// ".to_string());
    code.push("/// Return type and Java signature: `()` (`V`)".to_string());
    code.push(format!("pub fn {rust_setter_name}("));
    code.push("    &self,".to_string());
    code.push("    receiver: JObject<'a>,".to_string());
    code.push(format!("    {parameter_name}: {parameter_type},"));
    code.push(") -> JNIResult<()> {".to_string());
    code.push(format!("    let class_name = \"{}\";", class.path()));
    code.push(format!("    let field_name = \"{field_name}\";"));
    code.push(format!(
        "    let {parameter_name}_signature = \"{type_signature}\";"
    ));
    if is_signature_of_class_type(type_signature) {
        let parameter_class = &type_signature[1..(type_signature.len() - 1)];
        code.push(format!(
            "    let {parameter_name}_class_name = \"{parameter_class}\";"
        ));
    }
    code.push("".to_string());
    code.push(generate_variable_type_check("receiver", "class_name"));
    if is_signature_of_class_type(type_signature) {
        code.push(generate_variable_type_check(
            &parameter_name,
            &format!("{parameter_name}_class_name"),
        ));
    }
    code.push("    self.env.set_field(".to_string());
    code.push("        receiver,".to_string());
    code.push("        field_name,".to_string());
    code.push(format!("        {parameter_name}_signature,"));
    code.push(format!("        JValue::from({parameter_name})"));
    code.push("    )".to_string());
    code.push("}".to_string());

    code.join("\n") + "\n"
}

/// Generates Rust code to both retrieve and modify a value of
/// the specified field of a given object of the specified class
///
/// It works also for private fields and for inherited fields
///
/// It determines the type of the field by iterating over the
/// inheritance hierarchy and checking for a field with the matching name
///
/// It also generates runtime checks verifying
/// that the given object is of the specified class (or its descendant)
pub fn generate_field_getter_setter_for_class(
    env: &JNIEnv,
    class: &ClassName,
    field_name: &str,
) -> Result<String> {
    if trait_field_getter_setter::is_interface(env, class)? {
        return Err(ErrorKind::TraitField(class.full_name(), field_name.into(), true).into());
    }
    let field_signature = match hierarchy_field_lookup(env, class, field_name)? {
        Some(field) => {
            let field_type = env
                .call_method(field, "getType", "()Ljava/lang/Class;", &[])?
                .l()?;

            java_str_to_string(
                &env.get_string(
                    env.call_static_method(
                        "org/objectweb/asm/Type",
                        "getDescriptor",
                        "(Ljava/lang/Class;)Ljava/lang/String;",
                        &[JValue::Object(field_type)],
                    )?
                    .l()?
                    .into(),
                )?,
            )?
        }
        _ => return Err(ErrorKind::NoField(class.full_name(), field_name.into()).into()),
    };

    let setter_code = generate_field_getter(class, field_name, &field_signature);
    let getter_code = generate_field_setter(class, field_name, &field_signature);

    Ok(format!("{setter_code}\n{getter_code}"))
}
