#![feature(nll)]

extern crate walkdir;

use std::path::{PathBuf, Path};
use std::env;
use std::process::{Command, Stdio};
use std::str;

fn main(){
    if let Err(code) = process(std::env::args().skip(1).collect()) {
        std::process::exit(code);
    }
}

fn process(args: Vec<String>) -> Result<(), i32> {
    let mut prusti_driver_path = std::env::current_exe()
        .expect("current executable path invalid")
        .with_file_name("prusti-filter-driver");
    if cfg!(windows) {
        prusti_driver_path.set_extension("exe");
    }

    let prusti_sysroot = prusti_sysroot().expect(
        &format!("Failed to find Rust's sysroot for Prusti")
    );

    let compiler_lib = prusti_sysroot.join("lib");

    let prusti_home = prusti_driver_path.parent().expect("Failed to find Prusti's home");

    let prusti_contracts_lib = find_prusti_contracts(&prusti_home).expect(
        "Failed to find prusti_contracts library in Prusti's home"
    );

    let mut cmd = Command::new(&prusti_driver_path);
    let has_no_color_arg = args.iter().find(|&x| x == "--color" || x.starts_with("--color=")).is_none();
    cmd.args(args);
    if has_no_color_arg {
        cmd.args(&["--color", "always"]);
    }
    cmd.env("SYSROOT", &prusti_sysroot);
    cmd.env("PRUSTI_CONTRACTS_LIB", &prusti_contracts_lib);

    if let Some(target) = option_env!("TARGET") {
        let rustlib_path = prusti_sysroot
            .join("lib")
            .join("rustlib")
            .join(target)
            .join("lib");
        add_to_loader_path(vec![rustlib_path, compiler_lib], &mut cmd);
    } else {
        add_to_loader_path(vec![compiler_lib], &mut cmd);
    }

    let mut child = cmd
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .spawn().expect("could not run prusti-filter-driver");

    let exit_status = child.wait().expect("failed to wait for prusti-filter-driver?");

    if exit_status.success() {
        Ok(())
    } else {
        Err(exit_status.code().unwrap_or(-1))
    }
}

/// Append paths to the loader environment variable
fn add_to_loader_path(paths: Vec<PathBuf>, cmd: &mut Command) {
    #[cfg(target_os = "windows")]
    const LOADER_PATH: &str = "PATH";
    #[cfg(target_os = "linux")]
    const LOADER_PATH: &str = "LD_LIBRARY_PATH";
    #[cfg(target_os = "macos")]
    const LOADER_PATH: &str = "DYLD_FALLBACK_LIBRARY_PATH";
    env_prepend_path(LOADER_PATH, paths, cmd);
}

/// Prepend paths to an environment variable
pub fn env_prepend_path(name: &str, value: Vec<PathBuf>, cmd: &mut Command) {
    let old_value = env::var_os(name);
    let mut parts: Vec<PathBuf>;
    if let Some(ref v) = old_value {
        parts = value;
        parts.extend(env::split_paths(v).collect::<Vec<_>>());
    } else {
        parts = value;
    }
    match env::join_paths(parts) {
        Ok(new_value) => {
            cmd.env(name, new_value);
        }
        Err(err) => panic!("Error: {:?}", err),
    }
}

/// Find Prusti's sysroot
fn prusti_sysroot() -> Option<PathBuf> {
    Command::new("rustup")
        .arg("run")
        .arg(include_str!("../../rust-toolchain").trim())
        .arg("rustc")
        .arg("--print")
        .arg("sysroot")
        .output()
        .ok()
        .and_then(|out| { print!("{}", String::from_utf8(out.stderr).ok().unwrap()); String::from_utf8(out.stdout).ok() })
        .map(|s| PathBuf::from(s.trim().to_owned()))
}

/// Find the prusti-contracts library
fn find_prusti_contracts<S: AsRef<Path>>(path: S) -> Option<PathBuf> {
    let walker = walkdir::WalkDir::new(path).follow_links(true);

    for entry in walker {
        let entry = match entry {
            Ok(entry) => entry,
            Err(_e) => continue,
        };

        let file_name = entry.file_name().to_str().unwrap_or("");
        let extension = entry.path().extension().and_then(|x| x.to_str()).unwrap_or("");

        if extension == "rlib" && file_name.starts_with("libprusti_contracts") {
            return Some(entry.path().into());
        }
    }

    None
}
