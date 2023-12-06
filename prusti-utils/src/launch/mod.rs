// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![deny(unused_must_use)]
use serde::Deserialize;
use std::{
    env,
    path::{Path, PathBuf},
    process::Command,
};

pub mod job;

/// Determines which crates in `./prusti-contracts` have their specs re-exported
/// for `prusti-rustc`.
pub const PRUSTI_LIBS: [&str; 2] = ["prusti-contracts", "prusti-std"];

#[cfg(debug_assertions)]
pub const BUILD_MODE: &str = "debug";

#[cfg(not(debug_assertions))]
pub const BUILD_MODE: &str = "release";

pub fn get_current_executable_dir() -> PathBuf {
    env::current_exe()
        .expect("current executable path invalid")
        .parent()
        .expect("failed to obtain the folder of the current executable")
        .to_path_buf()
}

/// Finds the closest `target` directory in the current path.
/// This should be the target directory at the root of the repository,
/// i.e. `prusti-dev/target`.
fn get_target_dir(exe_dir: &Path) -> Option<PathBuf> {
    let mut root_dir = exe_dir;
    loop {
        if root_dir.file_name().unwrap() == "target" {
            return Some(root_dir.to_path_buf());
        }
        match root_dir.parent() {
            Some(parent) => root_dir = parent,
            None => return None,
        }
    }
}

pub fn get_prusti_contracts_build_target_dir(target_dir: &Path) -> PathBuf {
    target_dir.join("prusti-contracts").join(BUILD_MODE)
}

pub fn get_prusti_contracts_dir(exe_dir: &Path) -> Option<PathBuf> {
    let a_prusti_contracts_file = format!("lib{}.rlib", PRUSTI_LIBS[0].replace('-', "_"));

    if exe_dir.join(&a_prusti_contracts_file).exists() {
        // If this branch is entered, then this is the Prusti Artifact
        return Some(exe_dir.to_path_buf());
    } else if let Some(target_dir) = get_target_dir(exe_dir) {
        // If this branch is entered, then we're building Prusti
        let candidate = get_prusti_contracts_build_target_dir(&target_dir)
            .join("verify")
            .join(BUILD_MODE);
        if candidate.join(&a_prusti_contracts_file).exists() {
            return Some(candidate);
        }
    }
    None
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
        Err(err) => panic!("Error: {err:?}"),
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

    let content = include_str!("../../../rust-toolchain");
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
    let mut dir = base_dir;
    loop {
        if dir.join("viper_tools").is_dir() {
            let viper_tools_dir = dir.join("viper_tools");
            let backends_dir = viper_tools_dir.join("backends");
            if backends_dir.is_dir() {
                return Some(backends_dir);
            }
            let server_dir = viper_tools_dir.join("server");
            if server_dir.is_dir() {
                return Some(server_dir);
            }
        }
        match dir.parent() {
            Some(parent) => dir = parent,
            None => return None,
        }
    }
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

/// Checks if the current crate has a (transitive) dependency on `prusti-contracts`
/// and if that should lead to enabling the `prusti` feature when running cargo.
/// Will panic if there is a transitive dependency but not a direct one; in such a
/// case it wouldn't be possible to enable the feature.
pub fn enable_prusti_feature(cargo_path: &str) -> bool {
    let out = Command::new(cargo_path)
        .args(["tree", "--prefix", "depth", "-f", " [{f}] {p}"])
        .output()
        .unwrap_or_else(|_| panic!("Failed to run '{cargo_path} tree'"));
    // Expected stdout:
    // (error if line "2+ [] prusti-contracts " appears but no "0/1 [] prusti-contracts " line does):
    // 0 [] current-crate v0.1.0 (...)
    // 1 [] dependency-crate v0.1.0 (...)
    // 2 [] prusti-contracts v0.1.0 (...)
    // 1 [] prusti-contracts v0.1.0 (...) (*)
    if out.status.success() {
        let (mut has_direct_dep, mut has_indirect_dep) = (false, false);
        for line in String::from_utf8_lossy(&out.stdout).lines() {
            if let Some(depth) = classify_line(line) {
                has_direct_dep |= depth <= 1;
                has_indirect_dep |= depth > 1;
            }
        }
        assert!(has_direct_dep || !has_indirect_dep, "\n\nPrusti requires that the crate `prusti-contracts` is \
        included as a direct dependency of the current crate, so that it can enable the required features.\n\
        Please change the `[dependencies]` section of your `Cargo.toml` to include `prusti-contracts = ...`\n\n");
        has_direct_dep
    } else {
        // There is no dependency on `prusti-contracts`
        false
    }
}

fn classify_line(line: &str) -> Option<u32> {
    let mut line = line.split(' ');
    let depth = line.next()?;
    let feats = line.next()?;
    let cname = line.next()?;
    // We want to allow having crates which enable the `prusti` feature, thus anything that
    // depends on them need not add `prusti-contracts` as a direct dependency.
    if cname != "prusti-contracts" || feats != "[]" {
        return None;
    }
    depth.parse().ok()
}
