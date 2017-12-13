extern crate jni_gen;
extern crate env_logger;
extern crate error_chain;

use std::fs;
use std::env;
use jni_gen::*;
use error_chain::ChainedError;

fn main() {
    env_logger::init().expect("failed to initialize env_logger");
    let generated_dir = format!("{}/gen", env::var("CARGO_MANIFEST_DIR").unwrap());
    let asm_jar = env::var("ASM_JAR").unwrap();

    let mut viper_jars: Vec<String> = fs::read_dir("/usr/lib/viper/")
        .unwrap()
        .map(|x| x.unwrap().path().to_str().unwrap().to_owned())
        .collect();

    WrapperGenerator::new()
        .use_jar(&asm_jar)
        .use_jars(&mut viper_jars)
        .wrap_all(&vec![
            "java.lang.System",
            "java.io.PrintStream",
            "scala.Some",
            "scala.None$",
            "scala.Predef",
            "scala.Predef$",
            "scala.collection.mutable.ArraySeq",
            "viper.silicon.Silicon",
            "viper.silver.ast.Program",
            "viper.silver.ast.NoPosition$",
            "viper.silver.ast.NoInfo$",
            "viper.silver.ast.NoTrafos$",
        ])
        .generate(&generated_dir)
        .unwrap_or_else(|e| {
            panic!(format!("{}", e.display_chain().to_string()));
        });
}
