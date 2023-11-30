use std::env;
use std::path::PathBuf;

pub fn find_compiled_executable(name: &str) -> PathBuf {
    let target_directory = if cfg!(debug_assertions) {
        "debug"
    } else {
        "release"
    };

    let mut target_path = PathBuf::from("target");

    // For CI, however this is presumably also relevant for anyone
    // wishing to run tests for cross-compiled prusti
    if let Ok(triple) = env::var("COMPILATION_TARGET_PRUSTI") {
        target_path.push(triple);
    }

    target_path.push(target_directory);

    let executable_name = if cfg!(windows) {
        format!("{name}.exe")
    } else {
        name.to_string()
    };

    let mut local_driver_path = target_path.clone();
    local_driver_path.push(&executable_name);

    if local_driver_path.exists() {
        return local_driver_path;
    }

    let mut workspace_driver_path = PathBuf::from("..");
    workspace_driver_path.push(target_path);
    workspace_driver_path.push(&executable_name);

    if workspace_driver_path.exists() {
        return workspace_driver_path;
    }

    panic!(
        "Could not find the {target_directory:?} {executable_name:?} binary to be used in tests. \
        It might be that the project has not been compiled correctly."
    );
}

pub fn find_sysroot() -> String {
    // Taken from https://github.com/Manishearth/rust-clippy/pull/911.
    let home = option_env!("RUSTUP_HOME").or(option_env!("MULTIRUST_HOME"));
    let toolchain = option_env!("RUSTUP_TOOLCHAIN").or(option_env!("MULTIRUST_TOOLCHAIN"));
    match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{home}/toolchains/{toolchain}"),
        _ => option_env!("RUST_SYSROOT")
            .expect("need to specify RUST_SYSROOT env var or use rustup or multirust")
            .to_owned(),
    }
}
