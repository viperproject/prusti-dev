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
