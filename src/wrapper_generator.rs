use jni::JavaVM;
use jni::InitArgsBuilder;
use jni::JNIVersion;
use std::fs::OpenOptions;
use std::fs::create_dir_all;
use std::path::Path;
use std::io::prelude::*;
use errors::*;
use utils::*;
use gen_target::*;
use gen_mod::*;

pub struct WrapperGenerator {
    jars: Vec<String>,
    targets: Vec<String>,
}

impl Default for WrapperGenerator {
    fn default() -> Self {
        WrapperGenerator {
            jars: vec![],
            targets: vec![],
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

    pub fn wrap(&mut self, target_path: &str) -> &mut Self {
        self.targets.push(target_path.to_owned().replace(".", "/"));
        self
    }

    pub fn wrap_all(&mut self, target_paths: &Vec<&str>) -> &mut Self {
        for target_path in target_paths {
            self.targets.push(target_path.replace(".", "/").to_owned());
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
            let mod_code = generate_target_mod_code(&self.targets);
            let mod_path = format!("{}/mod.rs", out_dir);
            let mut mod_file = OpenOptions::new()
                .read(true)
                .write(true)
                .create(true)
                .truncate(true)
                .open(&mod_path)?;
            mod_file.write_all(mod_code.as_bytes())?;
        }

        for target in &self.targets {
            debug!("Generate wrapper for '{}'", target);
            let target_code = generate_target_code(&env, &target)?;
            let target_rel_mod_path = java_target_components(&target).join("/");
            let target_path = Path::new(out_dir)
                .join(target_rel_mod_path)
                .with_extension("rs");
            debug!(
                "Write wrapper for '{}' to '{}'",
                target,
                target_path.display()
            );
            if let Some(parent_path) = target_path.parent() {
                create_dir_all(parent_path)?;
            }
            let mut target_file = OpenOptions::new()
                .read(true)
                .write(true)
                .create(true)
                .truncate(true)
                .open(&target_path)?;
            target_file.write_all(target_code.as_bytes())?;
        }

        Ok(())
    }
}
