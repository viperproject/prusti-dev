extern crate jni_gen;
extern crate env_logger;
extern crate error_chain;

use std::env;
use jni_gen::*;
use error_chain::ChainedError;

fn main() {
    env_logger::init().expect("failed to initialize env_logger");
    let generated_dir = format!("{}/gen", env::var("CARGO_MANIFEST_DIR").unwrap());

    WrapperGenerator::new()
        .use_jar("/home/fpoli/opt/asm-3.3.1.jar")
        .use_jar("/usr/lib/viper/org.scala-lang.scala-library-2.11.8.jar")
        .use_jar("/usr/lib/viper/org.scala-lang.scala-reflect-2.11.8.jar")
        .use_jar("/usr/lib/viper/viper.silver-0.1-SNAPSHOT.jar")
        .wrap("viper.silver.ast.Program")
        .wrap("viper.silver.ast.Program$")
        .generate(&generated_dir)
        .unwrap_or_else(|e| {
            panic!(format!("{}", e.display_chain().to_string()));
        });
}
