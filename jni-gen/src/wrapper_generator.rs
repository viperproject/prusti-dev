// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    class_name::*,
    errors::Result as LocalResult,
    generators::{class::ClassGenerator, module::*},
    wrapper_spec::*,
};
use jni::{InitArgsBuilder, JNIVersion, JavaVM};
use log::debug;
use std::{fs::create_dir_all, io::prelude::*, path::Path};

#[derive(Default)]
pub struct WrapperGenerator {
    jars: Vec<String>,
    classes: Vec<ClassWrapperSpec>,
}

fn save_file_atomic(content: &str, temp_dir: &Path, file_path: &Path) -> LocalResult<()> {
    // Here we use `NamedTempFile` and `TempPath::persist` to make the write atomic.
    let mut mod_file = tempfile::NamedTempFile::new_in(temp_dir)?;
    mod_file.write_all(content.as_bytes())?;
    mod_file.into_temp_path().persist(file_path)?;
    Ok(())
}

impl WrapperGenerator {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn use_jar(&mut self, jar_path: &str) -> &mut Self {
        self.jars.push(jar_path.into());
        self
    }

    pub fn use_jars(&mut self, jar_paths: &mut Vec<String>) -> &mut Self {
        self.jars.append(jar_paths);
        self
    }

    pub fn wrap(&mut self, class: ClassWrapperSpec) -> &mut Self {
        self.classes.push(class);
        self
    }

    pub fn wrap_all(&mut self, classes: Vec<ClassWrapperSpec>) -> &mut Self {
        self.classes.extend(classes);
        self
    }

    #[tracing::instrument(level = "debug", skip(self))]
    pub fn generate(&mut self, out_dir: &Path) -> LocalResult<()> {
        let classpath_separator = if cfg!(windows) { ";" } else { ":" };

        let jvm_args = InitArgsBuilder::new()
            .version(JNIVersion::V8)
            .option(&format!(
                "-Djava.class.path={}",
                self.jars.join(classpath_separator)
            ))
            .build()?;

        let jvm = JavaVM::new(jvm_args)?;
        let env = jvm.attach_current_thread()?;

        //remove_dir_all(out_dir)?;
        create_dir_all(out_dir)?;
        create_dir_all(out_dir.join("builtins"))?;

        let utils_content = include_str!("../builtins/mod.rs");
        save_file_atomic(utils_content, out_dir, &out_dir.join("builtins/mod.rs"))?;

        for class in &self.classes {
            let class_name = class.get_name();
            debug!("Generate wrapper for '{}'", class_name.full_name());
            let class_rel_mod_path = {
                let mut class_components = class_name.full_components();
                let last_index = class_components.len() - 1;
                class_components.remove(last_index);
                class_components.join("/")
            };
            let class_path = Path::new(out_dir)
                .join(class_rel_mod_path)
                .join(format!("{}_wrapper.rs", class_name.rust_name()));
            debug!(
                "Write wrapper for '{}' to '{}'",
                class_name.full_name(),
                class_path.display()
            );
            if let Some(parent_path) = class_path.parent() {
                create_dir_all(parent_path)?;
            }

            let class_generator =
                ClassGenerator::new(&env, class_name.to_owned(), class.get_items().to_vec());
            let class_code = class_generator.generate()?;
            save_file_atomic(&class_code, out_dir, &class_path)?;
        }

        {
            let class_names: Vec<&ClassName> = self.classes.iter().map(|x| x.get_name()).collect();
            let mod_code = generate_module(class_names);
            save_file_atomic(&mod_code, out_dir, &out_dir.join("mod.rs"))?;
        }

        Ok(())
    }
}
