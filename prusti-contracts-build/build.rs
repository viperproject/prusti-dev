use std::{path::PathBuf, process::Command};

use prusti_utils::launch::get_prusti_contracts_build_target_dir;

fn executable_name(name: &str) -> String {
    #[cfg(windows)]
    let name = format!("{}.exe", name);

    #[cfg(not(windows))]
    let name = name.to_string();

    name
}

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

    let target = get_prusti_contracts_build_target_dir(&target);
    let bin_dir = target.join("bin");
    std::fs::create_dir_all(&bin_dir).unwrap();

    // Copies all files into `bin_dir`. `cargo_prusti` cannot be run directly
    // from std::env::var("CARGO_BIN_FILE_PRUSTI_LAUNCH_cargo-prusti")
    // because it requires `prusti-rustc` and `prusti-driver` to be in the same
    // path.
    for (krate, file) in [
        ("PRUSTI_LAUNCH", "cargo-prusti"),
        ("PRUSTI_LAUNCH", "prusti-rustc"),
        ("PRUSTI", "prusti-driver"),
    ] {
        let file_from = std::env::var(format!("CARGO_BIN_FILE_{krate}_{file}")).unwrap();
        let file_to = executable_name(file);
        let file_to = bin_dir.join(file_to);
        std::fs::copy(file_from, file_to).unwrap();
    }

    let cargo_prusti = bin_dir.join(executable_name("cargo-prusti"));
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
