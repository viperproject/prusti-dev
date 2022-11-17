use std::{env, path::Path};
use vir_gen::generate_vir;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=defs");
    for entry in walkdir::WalkDir::new("defs") {
        let entry = entry.unwrap();
        println!("cargo:rerun-if-changed={}", entry.path().display());
    }

    let out_dir = Path::new(&env::var("CARGO_MANIFEST_DIR").unwrap()).join("gen");
    generate_vir(Path::new("defs"), &out_dir);
}
