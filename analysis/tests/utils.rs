use std::path::PathBuf;

pub fn find_compiled_executable(name: &str) -> PathBuf {
    let target_directory = if cfg!(debug_assertions) {
        "debug"
    } else {
        "release"
    };
    let executable_name = if cfg!(windows) {
        format!("{name}.exe")
    } else {
        name.to_string()
    };
    let local_driver_path: PathBuf = ["target", target_directory, executable_name.as_str()]
        .iter()
        .collect();
    if local_driver_path.exists() {
        return local_driver_path;
    }
    let workspace_driver_path: PathBuf =
        ["..", "target", target_directory, executable_name.as_str()]
            .iter()
            .collect();
    if workspace_driver_path.exists() {
        return workspace_driver_path;
    }
    panic!(
        "Could not find the {target_directory:?} {executable_name:?} binary to be used in tests. \
        It might be that the project has not been compiled correctly."
    );
}

pub fn find_sysroot() -> String {
    // Taken from https://github.com/rust-lang/rust-clippy/commit/f5db351a1d502cb65f8807ec2c84f44756099ef3.
    let home = std::env::var("RUSTUP_HOME")
        .or_else(|_| std::env::var("MULTIRUST_HOME"))
        .ok();
    let toolchain = std::env::var("RUSTUP_TOOLCHAIN")
        .or_else(|_| std::env::var("MULTIRUST_TOOLCHAIN"))
        .ok();
    match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{home}/toolchains/{toolchain}"),
        _ => std::env::var("RUST_SYSROOT")
            .expect("need to specify RUST_SYSROOT env var or use rustup or multirust")
            .to_owned(),
    }
}
