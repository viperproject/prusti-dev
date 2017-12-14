extern crate jni_gen;
extern crate env_logger;
extern crate error_chain;

use std::env;
use jni_gen::*;
use error_chain::ChainedError;

fn main() {
    env_logger::init().expect("failed to initialize env_logger");
    let generated_dir = format!("{}/gen", env::var("CARGO_MANIFEST_DIR").unwrap());
    let asm_jar = env::var("ASM_JAR").unwrap();

    WrapperGenerator::new()
        .use_jar(&asm_jar)
        .wrap("java.lang.Integer")
        .wrap("java.util.Arrays")
        .generate(&generated_dir)
        .unwrap_or_else(|e| {
            panic!(format!("{}", e.display_chain().to_string()));
        });
}
