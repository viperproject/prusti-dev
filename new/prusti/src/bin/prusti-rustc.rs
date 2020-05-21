use std::env;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

/// Find the specified crate and construct the `--extern` compiler argument to
/// load it.
fn get_proc_macro_crate(path: &Path, crate_name: &str, file_extension: &str) -> String {
    let walker = walkdir::WalkDir::new(path).follow_links(true);

    let file_prefix = format!("lib{}-", crate_name);

    let mut candidates = Vec::new();
    for entry in walker {
        let entry = match entry {
            Ok(entry) => entry,
            Err(_e) => continue,
        };

        let file_name = entry.file_name().to_str().unwrap_or("");
        let extension = entry
            .path()
            .extension()
            .and_then(|x| x.to_str())
            .unwrap_or("");

        if extension == file_extension && file_name.starts_with(&file_prefix) {
            candidates.push(entry);
        }
    }
    let file_path = candidates
        .iter()
        .max_by_key(|entry| entry.metadata().unwrap().modified().unwrap())
        .map(|entry| entry.path())
        .unwrap_or_else(|| panic!("failed to find {} in {:?}", crate_name, path));

    format!(
        "{}={}",
        crate_name,
        file_path
            .as_os_str()
            .to_str()
            .expect("the file path contains invalid UTF-8")
    )
}

/// Find Prusti's sysroot
fn prusti_sysroot() -> Option<PathBuf> {
    Command::new("rustup")
        .arg("run")
        .arg(include_str!("../../../rust-toolchain").trim())
        .arg("rustc")
        .arg("--print")
        .arg("sysroot")
        .output()
        .ok()
        .and_then(|out| {
            print!("{}", String::from_utf8(out.stderr).ok().unwrap());
            String::from_utf8(out.stdout).ok()
        })
        .map(|s| PathBuf::from(s.trim().to_owned()))
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

fn process(mut args: Vec<String>) -> Result<(), i32> {
    let mut prusti_driver_path = std::env::current_exe()
        .expect("current executable path invalid")
        .with_file_name("prusti-driver");
    if cfg!(windows) {
        prusti_driver_path.set_extension("exe");
    }

    let prusti_sysroot =
        prusti_sysroot().expect(&format!("Failed to find Rust's sysroot for Prusti"));

    let compiler_lib = prusti_sysroot.join("lib");

    let prusti_home = prusti_driver_path
        .parent()
        .expect("Failed to find Prusti's home");

    let mut cmd = Command::new(&prusti_driver_path);

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

    let has_no_color_arg = args
        .iter()
        .find(|&x| x == "--color" || x.starts_with("--color="))
        .is_none();
    if has_no_color_arg {
        cmd.args(&["--color", "always"]);
    }
    if !args.iter().any(|s| s == "--sysroot") {
        args.push("--sysroot".to_owned());
        args.push(
            prusti_sysroot
                .into_os_string()
                .into_string()
                .expect("sysroot is not a valid utf-8 string"),
        );
    };

    cmd.args(args);

    if env::var_os("PRUSTI_LOAD_ALL_PROC_MACRO_CRATES").is_some() {
        cmd.arg("-L");
        cmd.arg(format!(
            "dependency={}/deps",
            prusti_home
                .as_os_str()
                .to_str()
                .expect("the Prusti HOME path contains invalid UTF-8")
        ));
        cmd.arg("--extern");
        cmd.arg(get_proc_macro_crate(
            &prusti_home,
            "prusti_contracts",
            "rlib",
        ));
    }
    cmd.arg("--extern");
    cmd.arg(get_proc_macro_crate(
        &prusti_home,
        "prusti_contracts_internal",
        "so",
    ));

    let mut child = cmd
        .stdout(Stdio::inherit()) // do not filter stdout
        .stderr(Stdio::inherit()) // do not filter stderr
        .spawn()
        .expect("could not run prusti-driver");

    let exit_status = child.wait().expect("failed to wait for prusti-driver?");

    if exit_status.success() {
        Ok(())
    } else {
        Err(exit_status.code().unwrap_or(-1))
    }
}

fn main() {
    if let Err(code) = process(std::env::args().skip(1).collect()) {
        std::process::exit(code);
    }
}
