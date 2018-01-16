use jni::JavaVM;
use jni::InitArgsBuilder;
use jni::JNIVersion;
use std::fs::OpenOptions;
use std::fs::create_dir_all;
use std::path::Path;
use std::io::prelude::*;
use errors::Result as LocalResult;
use utils::*;
use generators::module::*;
use class_name::*;
use generators::class::ClassGenerator;
use wrapper_spec::*;

pub struct WrapperGenerator {
    jars: Vec<String>,
    classes: Vec<ClassWrapperSpec>,
}

impl Default for WrapperGenerator {
    fn default() -> Self {
        WrapperGenerator {
            jars: vec![],
            classes: vec![],
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

    pub fn wrap(&mut self, class: ClassWrapperSpec) -> &mut Self {
        self.classes.push(class);
        self
    }

    pub fn wrap_all(&mut self, mut classes: Vec<ClassWrapperSpec>) -> &mut Self {
        self.classes.append(&mut classes);
        self
    }

    pub fn generate(&mut self, out_dir: &str) -> LocalResult<()> {
        debug!("Generate JNI wrappers in '{}'", out_dir);

        let jvm_args = InitArgsBuilder::new()
            .version(JNIVersion::V8)
            .option(&format!("-Djava.class.path={}", self.jars.join(":")))
            .option("-Xdebug")
            .build()?;

        let jvm = JavaVM::new(jvm_args)?;
        let env = jvm.attach_current_thread()?;

        create_dir_all(out_dir)?;

        let mut class_name_paths: Vec<String> = vec![];

        for class in self.classes.drain(..) {
            let class_name = ClassName::new(&class.full_class_name);
            class_name_paths.push(class_name.path());
            debug!("Generate wrapper for '{}'", class_name.full_name());
            let mut class_components = java_class_components(&class_name.path());
            let last_index = class_components.len() - 1;
            class_components.remove(last_index);
            let class_rel_mod_path = class_components.join("/");
            let class_path = Path::new(out_dir).join(class_rel_mod_path).join(format!(
                "{}_wrapper.rs",
                java_class_or_package_to_rust(&class_name.name())
            ));
            debug!(
                "Write wrapper for '{}' to '{}'",
                class.full_class_name,
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
            let class_generator = ClassGenerator::new(&env, class_name, class.items);
            let class_code = class_generator.generate()?;
            class_file.write_all(class_code.as_bytes())?;
        }

        {
            let mod_code = generate_module(class_name_paths);
            let mod_path = format!("{}/mod.rs", out_dir);
            let mut mod_file = OpenOptions::new()
                .read(true)
                .write(true)
                .create(true)
                .truncate(true)
                .open(&mod_path)?;
            mod_file.write_all(mod_code.as_bytes())?;
        }

        Ok(())
    }
}
