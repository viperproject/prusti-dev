extern crate env_logger;
extern crate error_chain;
extern crate jni_gen;
extern crate reqwest;
extern crate tempdir;

use std::env;
use jni_gen::*;
use error_chain::ChainedError;
use std::io::copy;
use std::fs::File;
use tempdir::TempDir;

fn main() {
    env_logger::init().expect("failed to initialize env_logger");
    let generated_dir = format!("{}/gen", env::var("CARGO_MANIFEST_DIR").unwrap());

    let deps_dir = TempDir::new("deps").unwrap_or_else(|e| {
        panic!(e.to_string());
    });

    // If ASM_JAR is set, use it. Otherwise, download asm.jar to a temporary location.
    let asm_jar = match env::var("ASM_JAR").ok() {
        Some(location) => location,
        None => {
            let target = "http://central.maven.org/maven2/asm/asm/3.3.1/asm-3.3.1.jar";
            let mut response = reqwest::get(target).unwrap_or_else(|e| {
                panic!(e.to_string());
            });
            let fname = deps_dir.path().join("asm.jar");
            let mut dest = File::create(fname.clone()).unwrap_or_else(|e| {
                panic!(e.to_string());
            });
            copy(&mut response, &mut dest).unwrap_or_else(|e| {
                panic!(e.to_string());
            });
            fname.to_str().unwrap().to_string()
        }
    };

    WrapperGenerator::new()
        .use_jar(&asm_jar)
        .wrap(java_class!("java.lang.Object"))
        .wrap_all(vec![
            java_class!("java.lang.Integer", vec![constructor!("(I)V")]),
            java_class!(
                "java.util.Arrays",
                vec![
                    method!("binarySearch", "([Ljava/lang/Object;Ljava/lang/Object;)I"),
                ]
            ),
        ])
        .generate(&generated_dir)
        .unwrap_or_else(|e| {
            panic!(e.display_chain().to_string());
        });

    // Remove the temporary directory
    drop(deps_dir);
}
