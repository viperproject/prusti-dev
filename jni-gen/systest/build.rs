use error_chain::ChainedError;
use jni_gen::*;
use std::{env, fs::File, io::copy, path::Path};
use tempfile::Builder;

fn main() {
    env_logger::init();
    let generated_dir = Path::new(&env::var("CARGO_MANIFEST_DIR").unwrap()).join("gen");

    let deps_dir = Builder::new().prefix("deps").tempdir().unwrap_or_else(|e| {
        panic!("{}", e);
    });

    // If ASM_JAR is set, use it. Otherwise, download asm.jar to a temporary location.
    let asm_jar = match env::var("ASM_JAR").ok() {
        Some(location) => location,
        None => {
            let target = "https://repo.maven.apache.org/maven2/asm/asm/3.3.1/asm-3.3.1.jar";
            let response = ureq::get(target).call().unwrap();
            let fname = deps_dir.path().join("asm.jar");
            let mut dest = File::create(fname.clone()).unwrap();
            copy(&mut response.into_reader(), &mut dest).unwrap();
            fname.to_str().unwrap().to_string()
        }
    };

    WrapperGenerator::new()
        .use_jar(&asm_jar)
        .wrap(java_class!("java.lang.Object"))
        .wrap_all(vec![
            java_class!("java.lang.Integer", vec![
                constructor!("(I)V"),
                field!("value"),
                method!("compareTo", "(Ljava/lang/Integer;)I"),
            ]),
            java_class!("java.util.Arrays", vec![
                method!("binarySearch", "([Ljava/lang/Object;Ljava/lang/Object;)I"),
            ]),
            java_class!("java.lang.Error", vec![
                constructor!("(Ljava/lang/String;)V"),
                method!("getMessage"),
                field!("detailMessage"),
            ]),
            java_class!("java.math.BigInteger", vec![
                method!("probablePrime"),
            ]),
        ])
        .generate(&generated_dir)
        .unwrap_or_else(|e| {
            panic!("{}", e.display_chain());
        });

    // Remove the temporary directory
    drop(deps_dir);
}
