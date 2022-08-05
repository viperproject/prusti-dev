// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![deny(unused_must_use)]

#[cfg(target_family = "unix")]
use nix::{
    sys::signal::{killpg, Signal},
    unistd::getpgrp,
};
use serde::Deserialize;
use std::{
    env,
    path::{Path, PathBuf},
    process::Command,
};

pub fn get_current_executable_dir() -> PathBuf {
    env::current_exe()
        .expect("current executable path invalid")
        .parent()
        .expect("failed to obtain the folder of the current executable")
        .to_path_buf()
}

/// Append paths to the loader environment variable
pub fn add_to_loader_path(paths: Vec<PathBuf>, cmd: &mut Command) {
    #[cfg(target_os = "windows")]
    const LOADER_PATH: &str = "PATH";
    #[cfg(target_os = "linux")]
    const LOADER_PATH: &str = "LD_LIBRARY_PATH";
    #[cfg(target_os = "macos")]
    const LOADER_PATH: &str = "DYLD_FALLBACK_LIBRARY_PATH";
    env_prepend_path(LOADER_PATH, paths, cmd);
}

/// Prepend paths to an environment variable
fn env_prepend_path(name: &str, value: Vec<PathBuf>, cmd: &mut Command) {
    let old_value = env::var_os(name);
    let mut parts = value;
    if let Some(ref v) = old_value {
        parts.extend(env::split_paths(v).collect::<Vec<_>>());
    };
    match env::join_paths(parts) {
        Ok(new_value) => {
            cmd.env(name, new_value);
        }
        Err(err) => panic!("Error: {:?}", err),
    }
}

/// Find the sub-folder containing the JVM dynamic library
pub fn find_libjvm<S: AsRef<Path>>(path: S) -> Option<PathBuf> {
    #[cfg(target_os = "windows")]
    const EXPECTED_JVM_FILENAME: &str = "jvm.dll";
    #[cfg(target_os = "linux")]
    const EXPECTED_JVM_FILENAME: &str = "libjvm.so";
    // On MacOS, we need to link to libjli instead of libjvm as a workaround to a Java8 bug.
    // See: https://github.com/jni-rs/jni-rs/pull/230
    #[cfg(target_os = "macos")]
    const EXPECTED_JVM_FILENAME: &str = "libjli.dylib";

    let walker = walkdir::WalkDir::new(path).follow_links(true);

    for entry in walker {
        let entry = match entry {
            Ok(entry) => entry,
            Err(_e) => continue,
        };

        let file_name = entry.file_name().to_str().unwrap_or("");

        if file_name == EXPECTED_JVM_FILENAME {
            return entry.path().parent().map(Into::into);
        }
    }

    None
}

/// Find the Java home directory
pub fn find_java_home() -> Option<PathBuf> {
    Command::new("java")
        .arg("-XshowSettings:properties")
        .arg("-version")
        .output()
        .ok()
        .and_then(|output| {
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            for line in stdout.lines().chain(stderr.lines()) {
                if line.contains("java.home") {
                    let pos = line.find('=').unwrap() + 1;
                    let path = line[pos..].trim();
                    return Some(PathBuf::from(path));
                }
            }
            None
        })
}

pub fn get_rust_toolchain_channel() -> String {
    #[derive(Deserialize)]
    struct RustToolchainFile {
        toolchain: RustToolchain,
    }

    #[derive(Deserialize)]
    struct RustToolchain {
        channel: String,
        #[allow(dead_code)]
        components: Option<Vec<String>>,
    }

    let content = include_str!("../../rust-toolchain");
    // Be ready to accept TOML format
    // See: https://github.com/rust-lang/rustup/pull/2438
    if content.starts_with("[toolchain]") {
        let rust_toolchain: RustToolchainFile =
            toml::from_str(content).expect("failed to parse rust-toolchain file");
        rust_toolchain.toolchain.channel
    } else {
        content.trim().to_string()
    }
}

/// Find Prusti's sysroot
pub fn prusti_sysroot() -> Option<PathBuf> {
    match env::var("RUST_SYSROOT") {
        Ok(prusti_sysroot) => Some(PathBuf::from(prusti_sysroot)),
        Err(_) => get_sysroot_from_rustup(),
    }
}

fn get_sysroot_from_rustup() -> Option<PathBuf> {
    Command::new("rustup")
        .arg("run")
        .arg(get_rust_toolchain_channel())
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

/// Find Viper home
pub fn find_viper_home(base_dir: &Path) -> Option<PathBuf> {
    let candidates = vec![
        base_dir.join("viper_tools").join("server"),
        base_dir
            .join("..")
            .join("..")
            .join("viper_tools")
            .join("server"),
        base_dir.join("viper_tools").join("backends"),
        base_dir
            .join("..")
            .join("..")
            .join("viper_tools")
            .join("backends"),
        base_dir
            .join("..")
            .join("..")
            .join("..")
            .join("viper_tools")
            .join("backends"),
    ];

    candidates.into_iter().find(|candidate| candidate.is_dir())
}

/// Find Z3 executable
pub fn find_z3_exe(base_dir: &Path) -> Option<PathBuf> {
    let mut candidates = vec![
        base_dir
            .join("viper_tools")
            .join("z3")
            .join("bin")
            .join("z3"),
        base_dir
            .join("..")
            .join("..")
            .join("viper_tools")
            .join("z3")
            .join("bin")
            .join("z3"),
    ];

    if cfg!(windows) {
        candidates.iter_mut().for_each(|x| {
            x.set_extension("exe");
        });
    }

    candidates.into_iter().find(|candidate| candidate.is_file())
}

#[cfg(target_family = "unix")]
pub fn sigint_handler() {
    // Killing the process group terminates the process tree
    killpg(getpgrp(), Signal::SIGKILL).expect("Error killing process tree.");
}

#[cfg(target_family = "windows")]
pub fn sigint_handler() {
    use std::process::{self, Stdio};

    // Kill process tree rooted at prusti-server.exe
    let pid: &str = &*process::id().to_string();

    Command::new("TASKKILL")
        .args(&["/PID", pid, "/T", "/F"])
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .expect("Error killing process tree.");
}

pub fn set_environment_settings(
    cmd: &mut Command,
    current_executable_dir: &Path,
    java_home: &Path,
) {
    set_smt_solver_path_setting(cmd, current_executable_dir);
    set_smt_solver_wrapper_path_setting(cmd, current_executable_dir);
    set_boogie_path_setting(cmd);
    set_viper_home_setting(cmd, current_executable_dir);
    set_java_home_setting(cmd, java_home)
}

pub fn set_smt_solver_path_setting(cmd: &mut Command, current_executable_dir: &Path) {
    let z3_exe = if let Ok(path) = env::var("Z3_EXE") {
        path.into()
    } else if let Some(path) = find_z3_exe(current_executable_dir) {
        path
    } else {
        panic!(
            "Could not find the Z3 executable. \
            Please set the Z3_EXE environment variable, which should contain the path of a \
            Z3 executable."
        );
    };
    cmd.env("PRUSTI_SMT_SOLVER_PATH", z3_exe);
}

pub fn set_smt_solver_wrapper_path_setting(cmd: &mut Command, current_executable_dir: &Path) {
    let mut prusti_smt_wrapper_path = current_executable_dir.join("prusti-smt-solver");
    if cfg!(windows) {
        prusti_smt_wrapper_path.set_extension("exe");
    }
    cmd.env("PRUSTI_SMT_SOLVER_WRAPPER_PATH", prusti_smt_wrapper_path);
}

pub fn set_boogie_path_setting(cmd: &mut Command) {
    if let Ok(path) = env::var("BOOGIE_EXE") {
        cmd.env("PRUSTI_BOOGIE_PATH", path);
    }
}

pub fn set_viper_home_setting(cmd: &mut Command, current_executable_dir: &Path) {
    let viper_home = if let Ok(path) = env::var("VIPER_HOME") {
        path.into()
    } else if let Some(viper_home) = find_viper_home(current_executable_dir) {
        viper_home
    } else {
        panic!(
            "Could not find the Viper home. \
            Please set the VIPER_HOME environment variable, which should contain the path of \
            the folder that contains all Viper JAR files."
        );
    };
    cmd.env("PRUSTI_VIPER_HOME", viper_home);
}

pub fn set_java_home_setting(cmd: &mut Command, java_home: &Path) {
    cmd.env("PRUSTI_JAVA_HOME", java_home);
}
