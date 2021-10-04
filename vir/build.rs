use proc_macro2::TokenStream;
use quote::quote;
use std::{
    env,
    io::Write,
    path::Path,
    process::{Command, Stdio},
};
use vir_gen::define_vir;

/// Try to pretty-print a tokenstream by piping it through `rustfmt`.
fn pretty_print_tokenstream(tokens: &TokenStream) -> Option<Vec<u8>> {
    let mut child = Command::new("rustfmt")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .ok()?;
    {
        let stdin = child.stdin.as_mut()?;
        stdin.write_all(tokens.to_string().as_bytes()).ok()?;
    }
    child.wait_with_output().ok().map(|o| o.stdout)
}

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=defs");
    for entry in walkdir::WalkDir::new("defs") {
        let entry = entry.unwrap();
        println!("cargo:rerun-if-changed={}", entry.path().display());
    }

    let root = quote! { components =>
        pub mod high;
        pub mod polymorphic;
    };
    let tokens = define_vir(root, Path::new("defs/root.rs"));
    let out_dir = Path::new(&env::var("CARGO_MANIFEST_DIR").unwrap()).join("gen");
    std::fs::create_dir_all(&out_dir).unwrap();
    let dest_path = Path::new(&out_dir).join("vir_gen.rs");
    let mut file = std::fs::File::create(dest_path).unwrap();
    if let Some(gen_code) = pretty_print_tokenstream(&tokens) {
        file.write_all(&gen_code).unwrap();
    } else {
        file.write_all(tokens.to_string().as_bytes()).unwrap();
    }
}
