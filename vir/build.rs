  
use quote::quote;
use std::env;
use std::io::Write;
use std::path::Path;
use svirpti_vir_generate::define_vir;

fn main() {
    println!("cargo:rerun-if-changed=defs");
    for entry in walkdir::WalkDir::new("defs") {
        let entry = entry.unwrap();
        println!("cargo:rerun-if-changed={}", entry.path().display());
    }

    let root = quote! { components =>
    };
    let tokens = define_vir(root, Path::new("defs/root.rs"));
    // let definition = parse_schema(Path::new("src/schema.dl"), Path::new("src/derived.dl"));
    let out_dir = env::var("OUT_DIR").unwrap();
    let dest_path = Path::new(&out_dir).join("vir.rs");
    // generate_definition(&dest_path, definition);
    let mut file = std::fs::File::create(dest_path).unwrap();
    file.write_all(tokens.to_string().as_bytes()).unwrap();
}
