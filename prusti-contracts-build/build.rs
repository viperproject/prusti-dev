use std::{path::PathBuf, process::Command};

fn main() {
    // Rerun if running with e.g. cargo clippy
    println!("cargo:rerun-if-env-changed=RUSTC_WORKSPACE_WRAPPER");

    // Rerun if any of the `prusti-contracts` crates change
    let prusti_contracts = ["..", "prusti-contracts"].iter().collect::<PathBuf>();
    let files = std::fs::read_dir(&prusti_contracts).unwrap();
    for file in files {
        let file = file.unwrap();
        let filename = file.file_name();
        let filename = filename.to_string_lossy();
        if filename != "target" {
            println!("cargo:rerun-if-changed={}", file.path().to_string_lossy());
        }
    }

    // In theory we should build to here (i.e. set `CARGO_TARGET_DIR` to this),
    // but this is hard to find for linking. So instead build to the `prusti-contracts` dir.
    let _out_dir = std::env::var("OUT_DIR").unwrap();
    // println!("cargo:warning=out_dir: {}", _out_dir);

    let target = prusti_contracts.join("target").join("verify");
    force_reexport_specs(target.as_path());

    // Copy just-built binaries to `target/dir` dir
    let dir = if cfg!(debug_assertions) {
        "debug"
    } else {
        "release"
    };
    for (krate, file) in [
        ("PRUSTI_LAUNCH", "cargo-prusti"),
        ("PRUSTI_LAUNCH", "prusti-rustc"),
        ("PRUSTI", "prusti-driver"),
    ] {
        let file_from = std::env::var(format!("CARGO_BIN_FILE_{krate}_{file}")).unwrap();
        let file_to = format!("{file}{}", if cfg!(windows) { ".exe" } else { "" });
        let file_to = ["..", "target", dir, &file_to].iter().collect::<PathBuf>();
        std::fs::copy(file_from, file_to).unwrap();
    }

    // Run `cargo-prusti`
    let cargo_prusti = format!("cargo-prusti{}", if cfg!(windows) { ".exe" } else { "" });
    let cargo_prusti = ["..", "target", dir, &cargo_prusti]
        .iter()
        .collect::<PathBuf>();
    let arg = "--release";
    // Not a warning but no other way to print to console
    println!(
        "cargo:warning=Building `prusti-contracts` with '{} {arg}', please wait.",
        cargo_prusti.to_string_lossy()
    );
    let status = Command::new(&cargo_prusti)
        .current_dir(&prusti_contracts)
        .arg(arg)
        .status()
        .expect("Failed to run cargo-prusti!");
    assert!(status.success());
}

/// Cargo will rebuild prusti-contracts if any of those files changed, however we also want to
/// reexport specs if any of the `cargo-prusti`/`prusti-{rustc,driver}` changed, and so
/// we manually force that here by deleting the `PRUSTI_LIBS` files.
fn force_reexport_specs(target: &std::path::Path) {
    if let Ok(files) = std::fs::read_dir(target.join("release").join("deps")) {
        let libs =
            prusti_utils::launch::PRUSTI_LIBS.map(|lib| format!("lib{}-", lib.replace('-', "_")));
        for file in files {
            let file = file.unwrap();
            let filename = file.file_name();
            let filename = filename.to_string_lossy();
            if libs.iter().any(|lib| filename.starts_with(lib)) {
                std::fs::remove_file(file.path()).ok();
            }
        }
    }
}
