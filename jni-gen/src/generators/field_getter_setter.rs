// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{class_name::*, errors::*, utils::*};
use jni::JNIEnv;

fn generate_type_check(type_signature: &str, type_name: &str, is_result: bool) -> String {
    if !type_signature.starts_with('L') {
        return "".to_string();
    }

    let type_class = &type_signature[1..(type_signature.len() - 1)];

    let type_check = vec![
        "    debug_assert!(".to_string(),
        "        self.env.is_instance_of(".to_string(),
        format!("            {type_name},"),
        format!("            self.env.find_class(\"{type_class}\")?,"),
        "        )?".to_string(),
        "    );".to_string(),
    ];

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

fn generate_result_type_check(return_signature: &str) -> String {
    generate_type_check(return_signature, "result", true)
}

fn generate_parameter_type_check(type_signature: &str, type_name: &str) -> String {
    generate_type_check(type_signature, type_name, false)
}

fn generate_field_getter(class_name: &ClassName, field_name: &str, type_signature: &str) -> String {
    let rust_getter_name = format!("get_{}", java_identifier_to_rust(field_name));
    let parameter_type = generate_jni_type(type_signature);

    vec![
        format!(
            "/// Returns the field `{}` of the scala class `{}`.",
            field_name,
            class_name.full_name()
        ),
        "///".to_string(),
        format!("/// Return type and Java signature: `{parameter_type}` (`{type_signature}`)"),
        format!("pub fn {rust_getter_name}("),
        "    &self,".to_string(),
        "    receiver: JObject<'a>,".to_string(),
        format!(") -> JNIResult<{parameter_type}> {{"),
        format!("    let class_name = \"{}\";", class_name.path()),
        format!("    let field_name = \"{field_name}\";"),
        format!("    let return_signature = \"{type_signature}\";"),
        "".to_string(),
        "    debug_assert!(".to_string(),
        "        self.env.is_instance_of(".to_string(),
        "            receiver,".to_string(),
        "            self.env.find_class(class_name)?,".to_string(),
        "        )?".to_string(),
        "    );".to_string(),
        "".to_string(),
        "    let result = self.env.get_field(".to_string(),
        "        receiver,".to_string(),
        "        field_name,".to_string(),
        "        return_signature,".to_string(),
        format!(
            "    ).and_then(|x| x.{}());",
            generate_jni_type_char(type_signature)
        ),
        "".to_string(),
        generate_result_type_check(type_signature),
        "    result".to_string(),
        "}".to_string(),
    ]
    .join("\n")
        + "\n"
}

fn generate_field_setter(class_name: &ClassName, field_name: &str, type_signature: &str) -> String {
    let rust_setter_name = format!("set_{}", java_identifier_to_rust(field_name));
    let parameter_name = format!("new_{field_name}");
    let parameter_type = generate_jni_type(type_signature);

    vec![
        format!(
            "/// Sets the field `{}` of the scala class `{}`.",
            field_name,
            class_name.full_name()
        ),
        "///".to_string(),
        "/// Type and Java signature of parameters:".to_string(),
        "///".to_string(),
        format!("/// - `{parameter_name}`: `{parameter_type}` (`{type_signature}`)"),
        "/// ".to_string(),
        "/// Return type and Java signature: `()` (`V`)".to_string(),
        format!("pub fn {rust_setter_name}("),
        "    &self,".to_string(),
        "    receiver: JObject<'a>,".to_string(),
        format!("    {parameter_name}: {parameter_type},"),
        ") -> JNIResult<()> {".to_string(),
        format!("    let class_name = \"{}\";", class_name.path()),
        format!("    let field_name = \"{field_name}\";"),
        format!("    let return_signature = \"{type_signature}\";"),
        "".to_string(),
        "    debug_assert!(".to_string(),
        "        self.env.is_instance_of(".to_string(),
        "            receiver,".to_string(),
        "            self.env.find_class(class_name)?,".to_string(),
        "        )?".to_string(),
        "    );".to_string(),
        "".to_string(),
        generate_parameter_type_check(type_signature, &parameter_name),
        "    self.env.set_field(".to_string(),
        "        receiver,".to_string(),
        "        field_name,".to_string(),
        "        return_signature,".to_string(),
        format!("        JValue::from({parameter_name})"),
        "    )".to_string(),
        "}".to_string(),
    ]
    .join("\n")
        + "\n"
}

pub fn generate_field_getter_setter(
    env: &JNIEnv,
    class_name: &ClassName,
    field_name: &str,
    type_signature: &str,
) -> Result<String> {
    env.get_field_id(class_name.path(), field_name, type_signature)
        .map(|_| ())?;

    let setter_code = generate_field_getter(class_name, field_name, type_signature);
    let getter_code = generate_field_setter(class_name, field_name, type_signature);

    Ok(format!("{setter_code}\n{getter_code}"))
}
