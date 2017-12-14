use jni::JavaVM;
use jni::InitArgsBuilder;
use jni::JNIVersion;
use std::fs::OpenOptions;
use std::fs::create_dir_all;
use std::path::Path;
use std::io::prelude::*;
use errors::*;
use utils::*;
use gen_class::*;
use gen_mod::*;

pub struct WrapperGenerator {
    jars: Vec<String>,
    classs: Vec<String>,
}

impl Default for WrapperGenerator {
    fn default() -> Self {
        WrapperGenerator {
            jars: vec![],
            classs: vec![],
        }
    }
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

    pub fn wrap(&mut self, class_path: &str) -> &mut Self {
        self.classs.push(class_path.to_owned().replace(".", "/"));
        self
    }

    pub fn wrap_all(&mut self, class_paths: &Vec<&str>) -> &mut Self {
        for class_path in class_paths {
            self.classs.push(class_path.replace(".", "/").to_owned());
        }
        self
    }

    pub fn generate(&mut self, out_dir: &str) -> Result<()> {
        debug!("Generate JNI wrappers in '{}'", out_dir);

        let jvm_args = InitArgsBuilder::new()
            .version(JNIVersion::V8)
            .option(&format!("-Djava.class.path={}", self.jars.join(":")))
            .option("-Xdebug")
            .build()?;

        let jvm = JavaVM::new(jvm_args)?;
        let env = jvm.attach_current_thread()?;

        create_dir_all(out_dir)?;

        {
            let mod_code = generate_mod_code(&self.classs);
            let mod_path = format!("{}/mod.rs", out_dir);
            let mut mod_file = OpenOptions::new()
                .read(true)
                .write(true)
                .create(true)
                .truncate(true)
                .open(&mod_path)?;
            mod_file.write_all(mod_code.as_bytes())?;
        }

        for class in &self.classs {
            debug!("Generate wrapper for '{}'", class);
            let class_code = generate_class_code(&env, &class)?;
            let mut class_components = java_class_components(&class);
            let last_index = class_components.len() - 1;
            let class_name = class_components.remove(last_index);
            let class_rel_mod_path = class_components.join("/");
            let class_path = Path::new(out_dir).join(class_rel_mod_path).join(format!(
                "class_{}.rs",
                class_name
            ));
            debug!(
                "Write wrapper for '{}' to '{}'",
                class,
                class_path.display()
            );
            if let Some(parent_path) = class_path.parent() {
                create_dir_all(parent_path)?;
            }
            let mut class_file = OpenOptions::new()
                .read(true)
                .write(true)
                .create(true)
                .truncate(true)
                .open(&class_path)?;
            class_file.write_all(class_code.as_bytes())?;
        }

        Ok(())
    }
}
