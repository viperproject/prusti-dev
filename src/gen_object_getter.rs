pub fn generate_scala_object_getter(target: &str) -> String {
    let last_target_char: Vec<char> = target.chars().rev().take(1).collect();
    if last_target_char[0] != '$' {
        "".to_owned()
    } else {
        vec![
            format!(
                "/// Wrapped getter of Scala object {}",
                target.replace("/", ".")
            ),
            "#[allow(dead_code)]".to_owned(),
            "pub fn new<'a>(env: &'a JNIEnv) -> Result<JObject<'a>> {".to_owned(),
            "    env.get_static_field(".to_owned(),
            format!("        \"{}\",", target),
            "        \"MODULE$\",".to_owned(),
            format!("        \"L{};\",", target),
            "    ).and_then(|x| x.l())".to_owned(),
            "}".to_owned(),
        ].join("\n") + "\n"
    }
}
