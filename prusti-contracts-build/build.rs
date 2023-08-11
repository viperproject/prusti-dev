use std::{path::PathBuf, process::Command};

fn main() {
    // Rerun if running with e.g. cargo clippy
    println!("cargo:rerun-if-env-changed=RUSTC_WORKSPACE_WRAPPER");

    // Rerun if any of the `prusti-contracts` crates change
    let prusti_contracts = ["..", "prusti-contracts"].iter().collect::<PathBuf>();
    println!(
        "cargo:rerun-if-changed={}",
        prusti_contracts.to_string_lossy()
    );

    let target: PathBuf = ["..", "target"].iter().collect();
    force_reexport_specs(target.join("verify").as_path());

    // Copy just-built binaries to `target/dir` dir
    let bin_dir = if cfg!(debug_assertions) {
        target.join("debug")
    } else {
        target.join("release")
    };
    for (krate, file) in [
        ("PRUSTI_LAUNCH", "cargo-prusti"),
        ("PRUSTI_LAUNCH", "prusti-rustc"),
        ("PRUSTI", "prusti-driver"),
    ] {
        let file_from = std::env::var(format!("CARGO_BIN_FILE_{krate}_{file}")).unwrap();
        let file_to = &format!("{file}{}", if cfg!(windows) { ".exe" } else { "" });
        let file_to = bin_dir.join(file_to);
        std::fs::copy(file_from, file_to).unwrap();
    }

    // Run `cargo-prusti`
    let cargo_prusti = format!("cargo-prusti{}", if cfg!(windows) { ".exe" } else { "" });
    let cargo_prusti = bin_dir.join(cargo_prusti);

    // In theory we should build to here (i.e. set `CARGO_TARGET_DIR` to this),
    // but this is hard to find for linking. So instead build to the `prusti-contracts` dir.
    // let out_dir = std::env::var("OUT_DIR").unwrap();
    // println!("cargo:warning=out_dir: {}", out_dir);

    let mut cmd = Command::new(cargo_prusti);
    cmd.env("CARGO_TARGET_DIR", target.as_os_str());
    cmd.current_dir(&prusti_contracts);
    if !cfg!(debug_assertions) {
        cmd.arg("--release");
    }
    cmd.env_remove("CARGO_MANIFEST_DIR");
    // This is set when running clippy, but we can't run clippy and prusti at the same time.
    cmd.env_remove("RUSTC_WORKSPACE_WRAPPER");

    // Not a warning but no other way to print to console
    println!("cargo:warning=Building `prusti-contracts` with {cmd:?}, please wait.",);

    let status = cmd.status().expect("Failed to run cargo-prusti!");
    assert!(status.success());
}

/// Cargo will rebuild prusti-contracts if any of those files changed, however we also want to
/// reexport specs if any of the `cargo-prusti`/`prusti-{rustc,driver}` changed, and so
/// we manually force that here by deleting the `PRUSTI_LIBS` files.
fn force_reexport_specs(target: &std::path::Path) {
    let deps_dir = if cfg!(debug_assertions) {
        target.join("debug").join("deps")
    } else {
        target.join("release").join("deps")
    };
    if let Ok(files) = std::fs::read_dir(deps_dir) {
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
