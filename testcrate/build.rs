extern crate env_logger;
extern crate error_chain;
extern crate jni_gen;

use std::env;
use jni_gen::*;
use error_chain::ChainedError;

fn main() {
    env_logger::init().expect("failed to initialize env_logger");
    let generated_dir = format!("{}/gen", env::var("CARGO_MANIFEST_DIR").unwrap());
    let asm_jar = env::var("ASM_JAR").unwrap();

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
            panic!(format!("{}", e.display_chain().to_string()));
        });
}
