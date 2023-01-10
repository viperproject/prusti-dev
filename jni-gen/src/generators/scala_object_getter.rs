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

    Ok(vec![
        format!(
            "/// Returns the unique instance of the Scala object `{}`.",
            class_name.full_name()
        ),
        "///".to_string(),
        format!(
            "/// Return type and Java signature: `JObject`, `L{};`",
            class_name.path()
        ),
        "pub fn singleton(&self) -> JNIResult<JObject<'a>> {".to_string(),
        format!("    let class_name = \"{}\";", class_name.path()),
        "    let field_name = \"MODULE$\";".to_string(),
        format!("    let field_signature = \"L{};\";", class_name.path()),
        "".to_string(),
        "static CLASS: OnceCell<GlobalRef> = OnceCell::new();".to_string(),
        "static STATIC_FIELD_ID: OnceCell<JStaticFieldID> = OnceCell::new();".to_string(),
        "static FIELD_TYPE: OnceCell<JavaType> = OnceCell::new();".to_string(),
        "let class = CLASS.get_or_try_init(|| {".to_string(),
        "    let class = self.env.find_class(class_name)?;".to_string(),
        "    self.env.new_global_ref(class)".to_string(),
        "})?;".to_string(),
        "let static_field_id = *STATIC_FIELD_ID.get_or_try_init(|| {".to_string(),
        "    self.env.get_static_field_id(".to_string(),
        "        class_name,".to_string(),
        "        field_name,".to_string(),
        "        field_signature,".to_string(),
        "    )".to_string(),
        "})?;".to_string(),
        "let field_type = FIELD_TYPE.get_or_try_init(|| {".to_string(),
        "    JavaType::from_str(field_signature)".to_string(),
        "})?.clone();".to_string(),
        "".to_string(),
        "    let result = self.env.get_static_field_unchecked(".to_string(),
        "        JClass::from(class.as_obj()),".to_string(),
        "        static_field_id,".to_string(),
        "        field_type,".to_string(),
        "    ).and_then(|x| x.l());".to_string(),
        "    result".to_string(),
        "}".to_string(),
    ]
    .join("\n")
        + "\n")
}
