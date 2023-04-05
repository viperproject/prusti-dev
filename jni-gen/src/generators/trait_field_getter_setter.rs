// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{class_name::*, errors::*, utils::*};
use jni::{objects::JValue, JNIEnv};

use super::method;

pub fn is_interface(env: &JNIEnv, class: &ClassName) -> Result<bool> {
    let class = env.find_class(class.path())?;
    Ok(env.call_method(class, "isInterface", "()Z", &[])?.z()?)
}

/// Generates Rust code to both retrieve and modify a value of
/// the specified field of a given object of the specified interface
///
/// Such fields are translated from Scala to Java as methods
pub fn generate_field_getter_setter_for_trait(
    env: &JNIEnv,
    class: &ClassName,
    field_name: &str,
) -> Result<String> {
    if !is_interface(env, class)? {
        return Err(ErrorKind::TraitField(class.full_name(), field_name.into(), false).into());
    }
    let setter_method_name = format!("{field_name}_$eq");
    let getter_method_name = field_name.to_string();
    let method::MethodInfo {
        method_signature: setter_method_signature,
        method: setter_method,
        is_static: setter_is_static,
    } = method::find_method(env, class, &setter_method_name, Option::None)?;
    let method::MethodInfo {
        method_signature: getter_method_signature,
        method: getter_method,
        is_static: getter_is_static,
    } = method::find_method(env, class, &getter_method_name, Option::None)?;

    // Check neither is static
    if setter_is_static || getter_is_static {
        return Err(ErrorKind::NoField(class.full_name(), field_name.into()).into());
    }

    let setter_parameters = env
        .call_method(
            setter_method,
            "getParameters",
            "()[Ljava/lang/reflect/Parameter;",
            &[],
        )?
        .l()?;
    let setter_num_parameters = env.get_array_length(*setter_parameters)?;

    // Check setter has 1 parameter, it has the name "x$1" and it returns a void
    if setter_num_parameters != 1 {
        return Err(ErrorKind::NoField(class.full_name(), field_name.into()).into());
    }

    let setter_parameter = env.get_object_array_element(*setter_parameters, 0)?;
    let setter_parameter_name = java_str_to_string(
        &env.get_string(
            env.call_method(setter_parameter, "getName", "()Ljava/lang/String;", &[])?
                .l()?
                .into(),
        )?,
    )?;

    if setter_parameter_name != "x$1" {
        return Err(ErrorKind::NoField(class.full_name(), field_name.into()).into());
    }

    // Check getter has 0 parameters
    let getter_parameters = env
        .call_method(
            getter_method,
            "getParameters",
            "()[Ljava/lang/reflect/Parameter;",
            &[],
        )?
        .l()?;
    let getter_num_parameters = env.get_array_length(*getter_parameters)?;

    if getter_num_parameters != 0 {
        return Err(ErrorKind::NoField(class.full_name(), field_name.into()).into());
    }

    // Check the setter parameter and getter return type match
    let setter_parameter_type = env
        .call_method(setter_parameter, "getType", "()Ljava/lang/Class;", &[])?
        .l()?;
    let setter_parameter_signature = java_str_to_string(
        &env.get_string(
            env.call_static_method(
                "org/objectweb/asm/Type",
                "getDescriptor",
                "(Ljava/lang/Class;)Ljava/lang/String;",
                &[JValue::Object(setter_parameter_type)],
            )?
            .l()?
            .into(),
        )?,
    )?;

    let getter_return_signature = get_return_signature(&getter_method_signature);

    if setter_parameter_signature != getter_return_signature {
        return Err(ErrorKind::NoField(class.full_name(), field_name.into()).into());
    }

    let getter_code = method::generate(
        class,
        &getter_method_name,
        &format!("get_{}", java_identifier_to_rust(field_name)),
        &getter_method_signature,
        &[],
        &[],
    );

    let setter_code = method::generate(
        class,
        &setter_method_name,
        &format!("set_{}", java_identifier_to_rust(field_name)),
        &setter_method_signature,
        &[format!("new_{field_name}")],
        &[setter_parameter_signature],
    );

    Ok(format!("{setter_code}\n{getter_code}"))
}
