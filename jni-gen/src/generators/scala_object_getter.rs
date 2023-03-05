// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{class_name::*, errors::Result};
use jni::JNIEnv;

pub fn generate_scala_object_getter(env: &JNIEnv, class_name: &ClassName) -> Result<String> {
    env.get_static_field_id(
        class_name.path(),
        "MODULE$",
        format!("L{};", class_name.path()),
    )
    .map(|_| ())?;

    let mut code: Vec<String> = vec![];
    code.push(format!(
        "/// Returns the unique instance of the Scala object `{}`.",
        class_name.full_name()
    ));
    code.push("///".to_string());
    code.push(format!(
        "/// Return type and Java signature: `JObject`, `L{};`",
        class_name.path()
    ));
    code.push("pub fn singleton(&self) -> JNIResult<JObject<'a>> {".to_string());
    code.push(format!("    let class_name = \"{}\";", class_name.path()));
    code.push("    let field_name = \"MODULE$\";".to_string());
    code.push(format!(
        "    let field_signature = \"L{};\";",
        class_name.path()
    ));
    code.push("".to_string());
    code.push("    static CLASS: OnceCell<GlobalRef> = OnceCell::new();".to_string());
    code.push(
        "    static STATIC_FIELD_ID: OnceCell<JStaticFieldID> = OnceCell::new();".to_string(),
    );
    code.push("    static FIELD_TYPE: OnceCell<JavaType> = OnceCell::new();".to_string());
    code.push("    let class = CLASS.get_or_try_init(|| {".to_string());
    code.push("        let class = self.env.find_class(class_name)?;".to_string());
    code.push("        self.env.new_global_ref(class)".to_string());
    code.push("    })?;".to_string());
    code.push("    let static_field_id = *STATIC_FIELD_ID.get_or_try_init(|| {".to_string());
    code.push("        self.env.get_static_field_id(".to_string());
    code.push("            class_name,".to_string());
    code.push("            field_name,".to_string());
    code.push("            field_signature,".to_string());
    code.push("        )".to_string());
    code.push("    })?;".to_string());
    code.push("    let field_type = FIELD_TYPE.get_or_try_init(|| {".to_string());
    code.push("        JavaType::from_str(field_signature)".to_string());
    code.push("    })?.clone();".to_string());
    code.push("".to_string());
    code.push("    let result = self.env.get_static_field_unchecked(".to_string());
    code.push("        JClass::from(class.as_obj()),".to_string());
    code.push("        static_field_id,".to_string());
    code.push("        field_type,".to_string());
    code.push("    ).and_then(|x| x.l());".to_string());
    code.push("    result".to_string());
    code.push("}".to_string());

    Ok(code.join("\n") + "\n")
}
