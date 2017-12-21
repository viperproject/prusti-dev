pub fn generate_scala_object_getter(class: &str) -> String {
    let last_class_char: Vec<char> = class.chars().rev().take(1).collect();
    if last_class_char[0] != '$' {
        "".to_owned()
    } else {
        vec![
            format!(
                "/// Returns the unique instance of the Scala object `{}`.",
                class.replace("/", ".")
            ),
            "///".to_owned(),
            format!(
                "/// Return type and Java signature: `JObject` (`L{};`)",
                class
            ),
            "#[allow(dead_code)]".to_owned(),
            "pub fn singleton(&self) -> JNIResult<JObject<'a>> {".to_owned(),
            "    self.env.get_static_field(".to_owned(),
            format!("        \"{}\",", class),
            "        \"MODULE$\",".to_owned(),
            format!("        \"L{};\",", class),
            "    ).and_then(|x| x.l())".to_owned(),
            "}".to_owned(),
        ].join("\n") + "\n"
    }
}
