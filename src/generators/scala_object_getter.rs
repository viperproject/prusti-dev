use errors::Result;
use jni::JNIEnv;
use class_name::*;

pub fn generate_scala_object_getter(env: &JNIEnv, class_name: &ClassName) -> Result<String> {
    env.get_static_field_id(
        class_name.path(),
        "MODULE$",
        format!("L{};", class_name.path()),
    ).map(|_| ())?;

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
        format!(
            "    let class = self.env.find_class(\"{}\")?;",
            class_name.path()
        ),
        "    self.env.get_static_field(".to_string(),
        "        class,".to_string(),
        "        \"MODULE$\",".to_string(),
        format!("        \"L{};\",", class_name.path()),
        "    ).and_then(|x| x.l())".to_string(),
        "}".to_string(),
    ].join("\n") + "\n")
}
