use std::path::PathBuf;

pub fn find_compiled_executable(name: &str) -> PathBuf {
    let target_directory = if cfg!(debug_assertions) {
        "debug"
    } else {
        "release"
    };
    let executable_name = if cfg!(windows) {
        format!("{}.exe", name)
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
        "Could not find the {:?} {:?} binary to be used in tests. \
        It might be that the project has not been compiled correctly.",
        target_directory, executable_name
    );
}

pub fn find_sysroot() -> String {
    // Taken from https://github.com/Manishearth/rust-clippy/pull/911.
    let home = option_env!("RUSTUP_HOME").or(option_env!("MULTIRUST_HOME"));
    let toolchain = option_env!("RUSTUP_TOOLCHAIN").or(option_env!("MULTIRUST_TOOLCHAIN"));
    match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{}/toolchains/{}", home, toolchain),
        _ => option_env!("RUST_SYSROOT")
            .expect("need to specify RUST_SYSROOT env var or use rustup or multirust")
            .to_owned(),
    }
}
